/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.functor.currying
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Products.Bifunctor

/-!
# Curry and uncurry, as functors.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `curry : ((C × D) ⥤ E) ⥤ (C ⥤ (D ⥤ E))` and `uncurry : (C ⥤ (D ⥤ E)) ⥤ ((C × D) ⥤ E)`,
and verify that they provide an equivalence of categories
`currying : (C ⥤ (D ⥤ E)) ≌ ((C × D) ⥤ E)`.

-/


namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C] {D : Type u₃}
  [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]

#print CategoryTheory.uncurry /-
/-- The uncurrying functor, taking a functor `C ⥤ (D ⥤ E)` and producing a functor `(C × D) ⥤ E`.
-/
@[simps]
def uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E
    where
  obj F :=
    { obj := fun X => (F.obj X.1).obj X.2
      map := fun X Y f => (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2
      map_comp' := fun X Y Z f g =>
        by
        simp only [prod_comp_fst, prod_comp_snd, functor.map_comp, nat_trans.comp_app,
          category.assoc]
        slice_lhs 2 3 => rw [← nat_trans.naturality]
        rw [category.assoc] }
  map F G T :=
    { app := fun X => (T.app X.1).app X.2
      naturality' := fun X Y f =>
        by
        simp only [prod_comp_fst, prod_comp_snd, category.comp_id, category.assoc, Functor.map_id,
          functor.map_comp, nat_trans.id_app, nat_trans.comp_app]
        slice_lhs 2 3 => rw [nat_trans.naturality]
        slice_lhs 1 2 => rw [← nat_trans.comp_app, nat_trans.naturality, nat_trans.comp_app]
        rw [category.assoc] }
#align category_theory.uncurry CategoryTheory.uncurry
-/

#print CategoryTheory.curryObj /-
/-- The object level part of the currying functor. (See `curry` for the functorial version.)
-/
def curryObj (F : C × D ⥤ E) : C ⥤ D ⥤ E
    where
  obj X :=
    { obj := fun Y => F.obj (X, Y)
      map := fun Y Y' g => F.map (𝟙 X, g) }
  map X X' f := { app := fun Y => F.map (f, 𝟙 Y) }
#align category_theory.curry_obj CategoryTheory.curryObj
-/

#print CategoryTheory.curry /-
/-- The currying functor, taking a functor `(C × D) ⥤ E` and producing a functor `C ⥤ (D ⥤ E)`.
-/
@[simps obj_obj_obj obj_obj_map obj_map_app map_app_app]
def curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E where
  obj F := curryObj F
  map F G T :=
    { app := fun X =>
        { app := fun Y => T.app (X, Y)
          naturality' := fun Y Y' g => by
            dsimp [curry_obj]
            rw [nat_trans.naturality] }
      naturality' := fun X X' f => by
        ext; dsimp [curry_obj]
        rw [nat_trans.naturality] }
#align category_theory.curry CategoryTheory.curry
-/

/- warning: category_theory.currying -> CategoryTheory.currying is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_4 : CategoryTheory.Category.{u3, u6} E], CategoryTheory.Equivalence.{max u4 u5 u3, max (max u4 u5) u3, max u1 (max u5 u3) u4 u2 u3 u5 u6, max (max u1 u2) u3 (max u4 u5) u6} (CategoryTheory.Functor.{u1, max u5 u3, u4, max u2 u3 u5 u6} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.category.{u1, max u5 u3, u4, max u2 u3 u5 u6} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.Functor.category.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4)
but is expected to have type
  forall {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_4 : CategoryTheory.Category.{u3, u6} E], CategoryTheory.Equivalence.{max (max u4 u5) u3, max (max u4 u5) u3, max (max (max (max (max (max u6 u5) u3) u2) u4) u5 u3) u1, max (max (max u6 u5 u4) u3) u1 u2} (CategoryTheory.Functor.{u1, max u5 u3, u4, max (max (max u6 u5) u3) u2} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.{max u1 u2, u3, max u5 u4, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.Functor.category.{u1, max u5 u3, u4, max (max (max u5 u6) u2) u3} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.category.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4)
Case conversion may be inaccurate. Consider using '#align category_theory.currying CategoryTheory.curryingₓ'. -/
-- create projection simp lemmas even though this isn't a `{ .. }`.
/-- The equivalence of functor categories given by currying/uncurrying.
-/
@[simps]
def currying : C ⥤ D ⥤ E ≌ C × D ⥤ E :=
  Equivalence.mk uncurry curry
    (NatIso.ofComponents
      (fun F =>
        NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => Iso.refl _) (by tidy))
          (by tidy))
      (by tidy))
    (NatIso.ofComponents (fun F => NatIso.ofComponents (fun X => eqToIso (by simp)) (by tidy))
      (by tidy))
#align category_theory.currying CategoryTheory.currying

/- warning: category_theory.flip_iso_curry_swap_uncurry -> CategoryTheory.flipIsoCurrySwapUncurry is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_4 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, max u5 u3, u4, max u2 u3 u5 u6} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)), CategoryTheory.Iso.{max u5 u4 u3, max u2 (max u4 u3) u5 u1 u3 u4 u6} (CategoryTheory.Functor.{u2, max u4 u3, u5, max u1 u3 u4 u6} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.category.{u2, max u4 u3, u5, max u1 u3 u4 u6} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.flip.{u1, u2, u3, u4, u5, u6} C _inst_2 D _inst_3 E _inst_4 F) (CategoryTheory.Functor.obj.{max (max u5 u4) u3, max u5 u4 u3, max (max u2 u1) u3 (max u5 u4) u6, max u2 (max u4 u3) u5 u1 u3 u4 u6} (CategoryTheory.Functor.{max u2 u1, u3, max u5 u4, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Functor.category.{max u2 u1, u3, max u5 u4, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Functor.{u2, max u4 u3, u5, max u1 u3 u4 u6} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.category.{u2, max u4 u3, u5, max u1 u3 u4 u6} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.curry.{u2, u1, u3, u5, u4, u6} D _inst_3 C _inst_2 E _inst_4) (CategoryTheory.Functor.comp.{max u2 u1, max u1 u2, u3, max u5 u4, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4 (CategoryTheory.Prod.swap.{u2, u1, u5, u4} D _inst_3 C _inst_2) (CategoryTheory.Functor.obj.{max u4 u5 u3, max (max u4 u5) u3, max u1 (max u5 u3) u4 u2 u3 u5 u6, max (max u1 u2) u3 (max u4 u5) u6} (CategoryTheory.Functor.{u1, max u5 u3, u4, max u2 u3 u5 u6} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.category.{u1, max u5 u3, u4, max u2 u3 u5 u6} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.Functor.category.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.uncurry.{u1, u2, u3, u4, u5, u6} C _inst_2 D _inst_3 E _inst_4) F)))
but is expected to have type
  forall {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_4 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, max u5 u3, u4, max (max (max u6 u5) u3) u2} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)), CategoryTheory.Iso.{max (max u4 u5) u3, max (max (max (max (max u4 u5) u6) u1) u2) u3} (CategoryTheory.Functor.{u2, max u4 u3, u5, max (max (max u6 u4) u3) u1} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.category.{u2, max u4 u3, u5, max (max (max u4 u6) u1) u3} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.flip.{u1, u2, u3, u4, u5, u6} C _inst_2 D _inst_3 E _inst_4 F) (Prefunctor.obj.{max (max (succ u4) (succ u5)) (succ u3), max (max (succ u4) (succ u5)) (succ u3), max (max (max (max (max u6 u4) u5) u3) u1) u2, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{max u2 u1, u3, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max (max u4 u5) u3, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{max u2 u1, u3, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Category.toCategoryStruct.{max (max u4 u5) u3, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{max u2 u1, u3, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Functor.category.{max u2 u1, u3, max u5 u4, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4))) (CategoryTheory.Functor.{u2, max u4 u3, u5, max (max (max u6 u4) u3) u1} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.CategoryStruct.toQuiver.{max (max u4 u5) u3, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{u2, max u4 u3, u5, max (max (max u6 u4) u3) u1} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Category.toCategoryStruct.{max (max u4 u5) u3, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{u2, max u4 u3, u5, max (max (max u6 u4) u3) u1} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.category.{u2, max u4 u3, u5, max (max (max u4 u6) u1) u3} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)))) (CategoryTheory.Functor.toPrefunctor.{max (max u4 u5) u3, max (max u4 u5) u3, max (max (max (max (max u6 u4) u5) u3) u1) u2, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{max u2 u1, u3, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Functor.category.{max u2 u1, u3, max u5 u4, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Functor.{u2, max u4 u3, u5, max (max (max u6 u4) u3) u1} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.category.{u2, max u4 u3, u5, max (max (max u4 u6) u1) u3} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.curry.{u2, u1, u3, u5, u4, u6} D _inst_3 C _inst_2 E _inst_4)) (CategoryTheory.Functor.comp.{max u1 u2, max u1 u2, u3, max u4 u5, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4 (CategoryTheory.Prod.swap.{u2, u1, u5, u4} D _inst_3 C _inst_2) (Prefunctor.obj.{max (max (succ u5) (succ u4)) (succ u3), max (max (succ u5) (succ u4)) (succ u3), max (max (max (max (max u6 u5) u4) u3) u2) u1, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{u1, max u5 u3, u4, max (max (max u6 u5) u3) u2} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.CategoryStruct.toQuiver.{max (max u5 u4) u3, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{u1, max u5 u3, u4, max (max (max u6 u5) u3) u2} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Category.toCategoryStruct.{max (max u5 u4) u3, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{u1, max u5 u3, u4, max (max (max u6 u5) u3) u2} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.category.{u1, max u5 u3, u4, max (max (max u5 u6) u2) u3} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)))) (CategoryTheory.Functor.{max u1 u2, u3, max u5 u4, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max (max u5 u4) u3, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{max u1 u2, u3, max u5 u4, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.Category.toCategoryStruct.{max (max u5 u4) u3, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{max u1 u2, u3, max u5 u4, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.Functor.category.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4))) (CategoryTheory.Functor.toPrefunctor.{max (max u5 u4) u3, max (max u5 u4) u3, max (max (max (max (max u6 u5) u4) u3) u2) u1, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{u1, max u5 u3, u4, max (max (max u6 u5) u3) u2} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.category.{u1, max u5 u3, u4, max (max (max u5 u6) u2) u3} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.{max u1 u2, u3, max u5 u4, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.Functor.category.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.uncurry.{u1, u2, u3, u4, u5, u6} C _inst_2 D _inst_3 E _inst_4)) F)))
Case conversion may be inaccurate. Consider using '#align category_theory.flip_iso_curry_swap_uncurry CategoryTheory.flipIsoCurrySwapUncurryₓ'. -/
/-- `F.flip` is isomorphic to uncurrying `F`, swapping the variables, and currying. -/
@[simps]
def flipIsoCurrySwapUncurry (F : C ⥤ D ⥤ E) : F.flip ≅ curry.obj (Prod.swap _ _ ⋙ uncurry.obj F) :=
  NatIso.ofComponents (fun d => NatIso.ofComponents (fun c => Iso.refl _) (by tidy)) (by tidy)
#align category_theory.flip_iso_curry_swap_uncurry CategoryTheory.flipIsoCurrySwapUncurry

/- warning: category_theory.uncurry_obj_flip -> CategoryTheory.uncurryObjFlip is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_4 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, max u5 u3, u4, max u2 u3 u5 u6} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)), CategoryTheory.Iso.{max (max u5 u4) u3, max (max u2 u1) u3 (max u5 u4) u6} (CategoryTheory.Functor.{max u2 u1, u3, max u5 u4, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Functor.category.{max u2 u1, u3, max u5 u4, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Functor.obj.{max u5 u4 u3, max (max u5 u4) u3, max u2 (max u4 u3) u5 u1 u3 u4 u6, max (max u2 u1) u3 (max u5 u4) u6} (CategoryTheory.Functor.{u2, max u4 u3, u5, max u1 u3 u4 u6} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.category.{u2, max u4 u3, u5, max u1 u3 u4 u6} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.{max u2 u1, u3, max u5 u4, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Functor.category.{max u2 u1, u3, max u5 u4, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.uncurry.{u2, u1, u3, u5, u4, u6} D _inst_3 C _inst_2 E _inst_4) (CategoryTheory.Functor.flip.{u1, u2, u3, u4, u5, u6} C _inst_2 D _inst_3 E _inst_4 F)) (CategoryTheory.Functor.comp.{max u2 u1, max u1 u2, u3, max u5 u4, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4 (CategoryTheory.Prod.swap.{u2, u1, u5, u4} D _inst_3 C _inst_2) (CategoryTheory.Functor.obj.{max u4 u5 u3, max (max u4 u5) u3, max u1 (max u5 u3) u4 u2 u3 u5 u6, max (max u1 u2) u3 (max u4 u5) u6} (CategoryTheory.Functor.{u1, max u5 u3, u4, max u2 u3 u5 u6} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.category.{u1, max u5 u3, u4, max u2 u3 u5 u6} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.Functor.category.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.uncurry.{u1, u2, u3, u4, u5, u6} C _inst_2 D _inst_3 E _inst_4) F))
but is expected to have type
  forall {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} C] {D : Type.{u5}} [_inst_3 : CategoryTheory.Category.{u2, u5} D] {E : Type.{u6}} [_inst_4 : CategoryTheory.Category.{u3, u6} E] (F : CategoryTheory.Functor.{u1, max u5 u3, u4, max (max (max u6 u5) u3) u2} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)), CategoryTheory.Iso.{max (max u4 u5) u3, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{max u2 u1, u3, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Functor.category.{max u1 u2, u3, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (Prefunctor.obj.{max (max (succ u4) (succ u5)) (succ u3), max (max (succ u4) (succ u5)) (succ u3), max (max (max (max (max u6 u4) u5) u3) u1) u2, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{u2, max u4 u3, u5, max (max (max u6 u4) u3) u1} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.CategoryStruct.toQuiver.{max (max u4 u5) u3, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{u2, max u4 u3, u5, max (max (max u6 u4) u3) u1} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Category.toCategoryStruct.{max (max u4 u5) u3, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{u2, max u4 u3, u5, max (max (max u6 u4) u3) u1} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.category.{u2, max u4 u3, u5, max (max (max u4 u6) u1) u3} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)))) (CategoryTheory.Functor.{max u2 u1, u3, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max (max u4 u5) u3, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{max u2 u1, u3, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Category.toCategoryStruct.{max (max u4 u5) u3, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{max u2 u1, u3, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Functor.category.{max u2 u1, u3, max u5 u4, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4))) (CategoryTheory.Functor.toPrefunctor.{max (max u4 u5) u3, max (max u4 u5) u3, max (max (max (max (max u6 u4) u5) u3) u1) u2, max (max (max (max (max u6 u4) u5) u3) u1) u2} (CategoryTheory.Functor.{u2, max u4 u3, u5, max (max (max u6 u4) u3) u1} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.category.{u2, max u4 u3, u5, max (max (max u4 u6) u1) u3} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} C _inst_2 E _inst_4) (CategoryTheory.Functor.category.{u1, u3, u4, u6} C _inst_2 E _inst_4)) (CategoryTheory.Functor.{max u2 u1, u3, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.Functor.category.{max u2 u1, u3, max u5 u4, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) E _inst_4) (CategoryTheory.uncurry.{u2, u1, u3, u5, u4, u6} D _inst_3 C _inst_2 E _inst_4)) (CategoryTheory.Functor.flip.{u1, u2, u3, u4, u5, u6} C _inst_2 D _inst_3 E _inst_4 F)) (CategoryTheory.Functor.comp.{max u1 u2, max u1 u2, u3, max u4 u5, max u4 u5, u6} (Prod.{u5, u4} D C) (CategoryTheory.prod.{u2, u1, u5, u4} D _inst_3 C _inst_2) (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4 (CategoryTheory.Prod.swap.{u2, u1, u5, u4} D _inst_3 C _inst_2) (Prefunctor.obj.{max (max (succ u5) (succ u4)) (succ u3), max (max (succ u5) (succ u4)) (succ u3), max (max (max (max (max u6 u5) u4) u3) u2) u1, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{u1, max u5 u3, u4, max (max (max u6 u5) u3) u2} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.CategoryStruct.toQuiver.{max (max u5 u4) u3, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{u1, max u5 u3, u4, max (max (max u6 u5) u3) u2} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Category.toCategoryStruct.{max (max u5 u4) u3, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{u1, max u5 u3, u4, max (max (max u6 u5) u3) u2} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.category.{u1, max u5 u3, u4, max (max (max u5 u6) u2) u3} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)))) (CategoryTheory.Functor.{max u1 u2, u3, max u5 u4, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max (max u5 u4) u3, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{max u1 u2, u3, max u5 u4, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.Category.toCategoryStruct.{max (max u5 u4) u3, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{max u1 u2, u3, max u5 u4, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.Functor.category.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4))) (CategoryTheory.Functor.toPrefunctor.{max (max u5 u4) u3, max (max u5 u4) u3, max (max (max (max (max u6 u5) u4) u3) u2) u1, max (max (max (max (max u6 u5) u4) u3) u2) u1} (CategoryTheory.Functor.{u1, max u5 u3, u4, max (max (max u6 u5) u3) u2} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.category.{u1, max u5 u3, u4, max (max (max u5 u6) u2) u3} C _inst_2 (CategoryTheory.Functor.{u2, u3, u5, u6} D _inst_3 E _inst_4) (CategoryTheory.Functor.category.{u2, u3, u5, u6} D _inst_3 E _inst_4)) (CategoryTheory.Functor.{max u1 u2, u3, max u5 u4, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.Functor.category.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_2 D _inst_3) E _inst_4) (CategoryTheory.uncurry.{u1, u2, u3, u4, u5, u6} C _inst_2 D _inst_3 E _inst_4)) F))
Case conversion may be inaccurate. Consider using '#align category_theory.uncurry_obj_flip CategoryTheory.uncurryObjFlipₓ'. -/
/-- The uncurrying of `F.flip` is isomorphic to
swapping the factors followed by the uncurrying of `F`. -/
@[simps]
def uncurryObjFlip (F : C ⥤ D ⥤ E) : uncurry.obj F.flip ≅ Prod.swap _ _ ⋙ uncurry.obj F :=
  NatIso.ofComponents (fun p => Iso.refl _) (by tidy)
#align category_theory.uncurry_obj_flip CategoryTheory.uncurryObjFlip

variable (B C D E)

#print CategoryTheory.whiskeringRight₂ /-
/-- A version of `category_theory.whiskering_right` for bifunctors, obtained by uncurrying,
applying `whiskering_right` and currying back
-/
@[simps]
def whiskeringRight₂ : (C ⥤ D ⥤ E) ⥤ (B ⥤ C) ⥤ (B ⥤ D) ⥤ B ⥤ E :=
  uncurry ⋙
    whiskeringRight _ _ _ ⋙ (whiskeringLeft _ _ _).obj (prodFunctorToFunctorProd _ _ _) ⋙ curry
#align category_theory.whiskering_right₂ CategoryTheory.whiskeringRight₂
-/

end CategoryTheory

