/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.functor.const
! leanprover-community/mathlib commit 34ee86e6a59d911a8e4f89b68793ee7577ae79c7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Opposites

/-!
# The constant functor

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`const J : C ⥤ (J ⥤ C)` is the functor that sends an object `X : C` to the functor `J ⥤ C` sending
every object in `J` to `X`, and every morphism to `𝟙 X`.

When `J` is nonempty, `const` is faithful.

We have `(const J).obj X ⋙ F ≅ (const J).obj (F.obj X)` for any `F : C ⥤ D`.
-/


-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory.Functor

variable (J : Type u₁) [Category.{v₁} J]

variable {C : Type u₂} [Category.{v₂} C]

#print CategoryTheory.Functor.const /-
/-- The functor sending `X : C` to the constant functor `J ⥤ C` sending everything to `X`.
-/
@[simps]
def const : C ⥤ J ⥤ C
    where
  obj X :=
    { obj := fun j => X
      map := fun j j' f => 𝟙 X }
  map X Y f := { app := fun j => f }
#align category_theory.functor.const CategoryTheory.Functor.const
-/

namespace Const

open Opposite

variable {J}

/- warning: category_theory.functor.const.op_obj_op -> CategoryTheory.Functor.const.opObjOp is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} C] (X : C), CategoryTheory.Iso.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.obj.{u2, max u3 u2, u4, max u1 u2 u3 u4} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2) (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.const.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (Opposite.op.{succ u4} C X)) (CategoryTheory.Functor.op.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.obj.{u2, max u3 u2, u4, max u1 u2 u3 u4} C _inst_2 (CategoryTheory.Functor.{u1, u2, u3, u4} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} J _inst_1 C _inst_2) (CategoryTheory.Functor.const.{u1, u2, u3, u4} J _inst_1 C _inst_2) X))
but is expected to have type
  forall {J : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} C] (X : C), CategoryTheory.Iso.{max u3 u2, max (max (max u3 u1) u2) u4} (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (Prefunctor.obj.{succ u2, max (succ u3) (succ u2), u4, max (max (max u3 u1) u2) u4} (Opposite.{succ u4} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (Opposite.{succ u4} C) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2))) (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max (max u3 u1) u4) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max (max u3 u1) u4) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)))) (CategoryTheory.Functor.toPrefunctor.{u2, max u3 u2, u4, max (max (max u3 u1) u4) u2} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2) (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.const.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2))) (Opposite.op.{succ u4} C X)) (CategoryTheory.Functor.op.{u1, u2, u3, u4} J _inst_1 C _inst_2 (Prefunctor.obj.{succ u2, max (succ u3) (succ u2), u4, max (max (max u3 u1) u2) u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} C (CategoryTheory.Category.toCategoryStruct.{u2, u4} C _inst_2)) (CategoryTheory.Functor.{u1, u2, u3, u4} J _inst_1 C _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max (max u3 u1) u4) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} J _inst_1 C _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max (max u3 u1) u4) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} J _inst_1 C _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u2, max u3 u2, u4, max (max (max u3 u1) u4) u2} C _inst_2 (CategoryTheory.Functor.{u1, u2, u3, u4} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} J _inst_1 C _inst_2) (CategoryTheory.Functor.const.{u1, u2, u3, u4} J _inst_1 C _inst_2)) X))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.const.op_obj_op CategoryTheory.Functor.const.opObjOpₓ'. -/
/-- The contant functor `Jᵒᵖ ⥤ Cᵒᵖ` sending everything to `op X`
is (naturally isomorphic to) the opposite of the constant functor `J ⥤ C` sending everything to `X`.
-/
@[simps]
def opObjOp (X : C) : (const Jᵒᵖ).obj (op X) ≅ ((const J).obj X).op
    where
  Hom := { app := fun j => 𝟙 _ }
  inv := { app := fun j => 𝟙 _ }
#align category_theory.functor.const.op_obj_op CategoryTheory.Functor.const.opObjOp

/- warning: category_theory.functor.const.op_obj_unop -> CategoryTheory.Functor.const.opObjUnop is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} C] (X : Opposite.{succ u4} C), CategoryTheory.Iso.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (CategoryTheory.Functor.obj.{u2, max u3 u2, u4, max u1 u2 u3 u4} C _inst_2 (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (CategoryTheory.Functor.const.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (Opposite.unop.{succ u4} C X)) (CategoryTheory.Functor.leftOp.{u1, u2, u3, u4} J _inst_1 C _inst_2 (CategoryTheory.Functor.obj.{u2, max u3 u2, u4, max u1 u2 u3 u4} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2) (CategoryTheory.Functor.{u1, u2, u3, u4} J _inst_1 (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u1, u2, u3, u4} J _inst_1 (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.const.{u1, u2, u3, u4} J _inst_1 (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) X))
but is expected to have type
  forall {J : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} C] (X : Opposite.{succ u4} C), CategoryTheory.Iso.{max u3 u2, max (max (max u3 u1) u2) u4} (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (Prefunctor.obj.{succ u2, max (succ u3) (succ u2), u4, max (max (max u3 u1) u2) u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} C (CategoryTheory.Category.toCategoryStruct.{u2, u4} C _inst_2)) (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max (max u3 u1) u4) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max (max u3 u1) u4) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u2, max u3 u2, u4, max (max (max u3 u1) u4) u2} C _inst_2 (CategoryTheory.Functor.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2) (CategoryTheory.Functor.const.{u1, u2, u3, u4} (Opposite.{succ u3} J) (CategoryTheory.Category.opposite.{u1, u3} J _inst_1) C _inst_2)) (Opposite.unop.{succ u4} C X)) (CategoryTheory.Functor.leftOp.{u1, u2, u3, u4} J _inst_1 C _inst_2 (Prefunctor.obj.{succ u2, max (succ u3) (succ u2), u4, max (max (max u3 u1) u2) u4} (Opposite.{succ u4} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} (Opposite.{succ u4} C) (CategoryTheory.Category.toCategoryStruct.{u2, u4} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2))) (CategoryTheory.Functor.{u1, u2, u3, u4} J _inst_1 (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max (max u3 u1) u4) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} J _inst_1 (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max (max u3 u1) u4) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} J _inst_1 (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u1, u2, u3, u4} J _inst_1 (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)))) (CategoryTheory.Functor.toPrefunctor.{u2, max u3 u2, u4, max (max (max u3 u1) u4) u2} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2) (CategoryTheory.Functor.{u1, u2, u3, u4} J _inst_1 (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u1, u2, u3, u4} J _inst_1 (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2)) (CategoryTheory.Functor.const.{u1, u2, u3, u4} J _inst_1 (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u2, u4} C _inst_2))) X))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.const.op_obj_unop CategoryTheory.Functor.const.opObjUnopₓ'. -/
/-- The contant functor `Jᵒᵖ ⥤ C` sending everything to `unop X`
is (naturally isomorphic to) the opposite of
the constant functor `J ⥤ Cᵒᵖ` sending everything to `X`.
-/
def opObjUnop (X : Cᵒᵖ) : (const Jᵒᵖ).obj (unop X) ≅ ((const J).obj X).leftOp
    where
  Hom := { app := fun j => 𝟙 _ }
  inv := { app := fun j => 𝟙 _ }
#align category_theory.functor.const.op_obj_unop CategoryTheory.Functor.const.opObjUnop

/- warning: category_theory.functor.const.op_obj_unop_hom_app -> CategoryTheory.Functor.const.opObjUnop_hom_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.const.op_obj_unop_hom_app CategoryTheory.Functor.const.opObjUnop_hom_appₓ'. -/
-- Lean needs some help with universes here.
@[simp]
theorem opObjUnop_hom_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).Hom.app j = 𝟙 _ :=
  rfl
#align category_theory.functor.const.op_obj_unop_hom_app CategoryTheory.Functor.const.opObjUnop_hom_app

/- warning: category_theory.functor.const.op_obj_unop_inv_app -> CategoryTheory.Functor.const.opObjUnop_inv_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.const.op_obj_unop_inv_app CategoryTheory.Functor.const.opObjUnop_inv_appₓ'. -/
@[simp]
theorem opObjUnop_inv_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).inv.app j = 𝟙 _ :=
  rfl
#align category_theory.functor.const.op_obj_unop_inv_app CategoryTheory.Functor.const.opObjUnop_inv_app

/- warning: category_theory.functor.const.unop_functor_op_obj_map -> CategoryTheory.Functor.const.unop_functor_op_obj_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.const.unop_functor_op_obj_map CategoryTheory.Functor.const.unop_functor_op_obj_mapₓ'. -/
@[simp]
theorem unop_functor_op_obj_map (X : Cᵒᵖ) {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
    (unop ((Functor.op (const J)).obj X)).map f = 𝟙 (unop X) :=
  rfl
#align category_theory.functor.const.unop_functor_op_obj_map CategoryTheory.Functor.const.unop_functor_op_obj_map

end Const

section

variable {D : Type u₃} [Category.{v₃} D]

/- warning: category_theory.functor.const_comp -> CategoryTheory.Functor.constComp is a dubious translation:
lean 3 declaration is
  forall (J : Type.{u4}) [_inst_1 : CategoryTheory.Category.{u1, u4} J] {C : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} C] {D : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} D] (X : C) (F : CategoryTheory.Functor.{u2, u3, u5, u6} C _inst_2 D _inst_3), CategoryTheory.Iso.{max u4 u3, max u1 u3 u4 u6} (CategoryTheory.Functor.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} J _inst_1 C _inst_2 D _inst_3 (CategoryTheory.Functor.obj.{u2, max u4 u2, u5, max u1 u2 u4 u5} C _inst_2 (CategoryTheory.Functor.{u1, u2, u4, u5} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u1, u2, u4, u5} J _inst_1 C _inst_2) (CategoryTheory.Functor.const.{u1, u2, u4, u5} J _inst_1 C _inst_2) X) F) (CategoryTheory.Functor.obj.{u3, max u4 u3, u6, max u1 u3 u4 u6} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.Functor.const.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.Functor.obj.{u2, u3, u5, u6} C _inst_2 D _inst_3 F X))
but is expected to have type
  forall (J : Type.{u4}) [_inst_1 : CategoryTheory.Category.{u1, u4} J] {C : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} C] {D : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} D] (X : C) (F : CategoryTheory.Functor.{u2, u3, u5, u6} C _inst_2 D _inst_3), CategoryTheory.Iso.{max u4 u3, max (max (max u6 u4) u3) u1} (CategoryTheory.Functor.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.Functor.comp.{u1, u2, u3, u4, u5, u6} J _inst_1 C _inst_2 D _inst_3 (Prefunctor.obj.{succ u2, max (succ u4) (succ u2), u5, max (max (max u4 u1) u2) u5} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} C (CategoryTheory.Category.toCategoryStruct.{u2, u5} C _inst_2)) (CategoryTheory.Functor.{u1, u2, u4, u5} J _inst_1 C _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u2, max (max (max u4 u1) u5) u2} (CategoryTheory.Functor.{u1, u2, u4, u5} J _inst_1 C _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u4 u2, max (max (max u4 u1) u5) u2} (CategoryTheory.Functor.{u1, u2, u4, u5} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u1, u2, u4, u5} J _inst_1 C _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u2, max u4 u2, u5, max (max (max u4 u1) u5) u2} C _inst_2 (CategoryTheory.Functor.{u1, u2, u4, u5} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u1, u2, u4, u5} J _inst_1 C _inst_2) (CategoryTheory.Functor.const.{u1, u2, u4, u5} J _inst_1 C _inst_2)) X) F) (Prefunctor.obj.{succ u3, max (succ u4) (succ u3), u6, max (max (max u4 u1) u3) u6} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} D (CategoryTheory.Category.toCategoryStruct.{u3, u6} D _inst_3)) (CategoryTheory.Functor.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u3, max (max (max u4 u1) u6) u3} (CategoryTheory.Functor.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u4 u3, max (max (max u4 u1) u6) u3} (CategoryTheory.Functor.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} J _inst_1 D _inst_3))) (CategoryTheory.Functor.toPrefunctor.{u3, max u4 u3, u6, max (max (max u4 u1) u6) u3} D _inst_3 (CategoryTheory.Functor.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.Functor.category.{u1, u3, u4, u6} J _inst_1 D _inst_3) (CategoryTheory.Functor.const.{u1, u3, u4, u6} J _inst_1 D _inst_3)) (Prefunctor.obj.{succ u2, succ u3, u5, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} C (CategoryTheory.Category.toCategoryStruct.{u2, u5} C _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} D (CategoryTheory.Category.toCategoryStruct.{u3, u6} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} C _inst_2 D _inst_3 F) X))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.const_comp CategoryTheory.Functor.constCompₓ'. -/
/-- These are actually equal, of course, but not definitionally equal
  (the equality requires F.map (𝟙 _) = 𝟙 _). A natural isomorphism is
  more convenient than an equality between functors (compare id_to_iso). -/
@[simps]
def constComp (X : C) (F : C ⥤ D) : (const J).obj X ⋙ F ≅ (const J).obj (F.obj X)
    where
  Hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
#align category_theory.functor.const_comp CategoryTheory.Functor.constComp

/-- If `J` is nonempty, then the constant functor over `J` is faithful. -/
instance [Nonempty J] : Faithful (const J : C ⥤ J ⥤ C)
    where map_injective' X Y f g e := NatTrans.congr_app e (Classical.arbitrary J)

end

end CategoryTheory.Functor

