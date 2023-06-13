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

#print CategoryTheory.Functor.const.opObjOp /-
/-- The contant functor `Jᵒᵖ ⥤ Cᵒᵖ` sending everything to `op X`
is (naturally isomorphic to) the opposite of the constant functor `J ⥤ C` sending everything to `X`.
-/
@[simps]
def opObjOp (X : C) : (const Jᵒᵖ).obj (op X) ≅ ((const J).obj X).op
    where
  Hom := { app := fun j => 𝟙 _ }
  inv := { app := fun j => 𝟙 _ }
#align category_theory.functor.const.op_obj_op CategoryTheory.Functor.const.opObjOp
-/

#print CategoryTheory.Functor.const.opObjUnop /-
/-- The contant functor `Jᵒᵖ ⥤ C` sending everything to `unop X`
is (naturally isomorphic to) the opposite of
the constant functor `J ⥤ Cᵒᵖ` sending everything to `X`.
-/
def opObjUnop (X : Cᵒᵖ) : (const Jᵒᵖ).obj (unop X) ≅ ((const J).obj X).leftOp
    where
  Hom := { app := fun j => 𝟙 _ }
  inv := { app := fun j => 𝟙 _ }
#align category_theory.functor.const.op_obj_unop CategoryTheory.Functor.const.opObjUnop
-/

#print CategoryTheory.Functor.const.opObjUnop_hom_app /-
-- Lean needs some help with universes here.
@[simp]
theorem opObjUnop_hom_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).Hom.app j = 𝟙 _ :=
  rfl
#align category_theory.functor.const.op_obj_unop_hom_app CategoryTheory.Functor.const.opObjUnop_hom_app
-/

#print CategoryTheory.Functor.const.opObjUnop_inv_app /-
@[simp]
theorem opObjUnop_inv_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).inv.app j = 𝟙 _ :=
  rfl
#align category_theory.functor.const.op_obj_unop_inv_app CategoryTheory.Functor.const.opObjUnop_inv_app
-/

#print CategoryTheory.Functor.const.unop_functor_op_obj_map /-
@[simp]
theorem unop_functor_op_obj_map (X : Cᵒᵖ) {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
    (unop ((Functor.op (const J)).obj X)).map f = 𝟙 (unop X) :=
  rfl
#align category_theory.functor.const.unop_functor_op_obj_map CategoryTheory.Functor.const.unop_functor_op_obj_map
-/

end Const

section

variable {D : Type u₃} [Category.{v₃} D]

#print CategoryTheory.Functor.constComp /-
/-- These are actually equal, of course, but not definitionally equal
  (the equality requires F.map (𝟙 _) = 𝟙 _). A natural isomorphism is
  more convenient than an equality between functors (compare id_to_iso). -/
@[simps]
def constComp (X : C) (F : C ⥤ D) : (const J).obj X ⋙ F ≅ (const J).obj (F.obj X)
    where
  Hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
#align category_theory.functor.const_comp CategoryTheory.Functor.constComp
-/

/-- If `J` is nonempty, then the constant functor over `J` is faithful. -/
instance [Nonempty J] : Faithful (const J : C ⥤ J ⥤ C)
    where map_injective' X Y f g e := NatTrans.congr_app e (Classical.arbitrary J)

end

end CategoryTheory.Functor

