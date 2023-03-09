/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.concrete_category.reflects_isomorphisms
! leanprover-community/mathlib commit 73dd4b5411ec8fafb18a9d77c9c826907730af80
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.ConcreteCategory.Basic
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms

/-!
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
whose forgetful functors both reflect isomorphisms, itself reflects isomorphisms.
-/


universe u

namespace CategoryTheory

instance : ReflectsIsomorphisms (forget (Type u)) where reflects X Y f i := i

variable (C : Type (u + 1)) [Category C] [ConcreteCategory.{u} C]

variable (D : Type (u + 1)) [Category D] [ConcreteCategory.{u} D]

/- warning: category_theory.reflects_isomorphisms_forget₂ -> CategoryTheory.reflectsIsomorphisms_forget₂ is a dubious translation:
lean 3 declaration is
  forall (C : Type.{succ u1}) [_inst_1 : CategoryTheory.Category.{u2, succ u1} C] [_inst_2 : CategoryTheory.ConcreteCategory.{u1, u2, succ u1} C _inst_1] (D : Type.{succ u1}) [_inst_3 : CategoryTheory.Category.{u3, succ u1} D] [_inst_4 : CategoryTheory.ConcreteCategory.{u1, u3, succ u1} D _inst_3] [_inst_5 : CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u2, u3} C D _inst_1 _inst_2 _inst_3 _inst_4] [_inst_6 : CategoryTheory.ReflectsIsomorphisms.{u2, u1, succ u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u2} C _inst_1 _inst_2)], CategoryTheory.ReflectsIsomorphisms.{u2, u3, succ u1, succ u1} C _inst_1 D _inst_3 (CategoryTheory.forget₂.{succ u1, succ u1, u2, u1, u3} C D _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)
but is expected to have type
  forall (C : Type.{succ u3}) [_inst_1 : CategoryTheory.Category.{u2, succ u3} C] [_inst_2 : CategoryTheory.ConcreteCategory.{u3, u2, succ u3} C _inst_1] (D : Type.{succ u3}) [_inst_3 : CategoryTheory.Category.{u1, succ u3} D] [_inst_4 : CategoryTheory.ConcreteCategory.{u3, u1, succ u3} D _inst_3] [_inst_5 : CategoryTheory.HasForget₂.{succ u3, succ u3, u3, u2, u1} C D _inst_1 _inst_2 _inst_3 _inst_4] [_inst_6 : CategoryTheory.ReflectsIsomorphisms.{u2, u3, succ u3, succ u3} C _inst_1 Type.{u3} CategoryTheory.types.{u3} (CategoryTheory.forget.{succ u3, u3, u2} C _inst_1 _inst_2)], CategoryTheory.ReflectsIsomorphisms.{u2, u1, succ u3, succ u3} C _inst_1 D _inst_3 (CategoryTheory.forget₂.{succ u3, succ u3, u2, u3, u1} C D _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)
Case conversion may be inaccurate. Consider using '#align category_theory.reflects_isomorphisms_forget₂ CategoryTheory.reflectsIsomorphisms_forget₂ₓ'. -/
-- This should not be an instance, as it causes a typeclass loop
-- with `category_theory.has_forget_to_Type`
/-- A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
where `forget C` reflects isomorphisms, itself reflects isomorphisms.
-/
theorem reflectsIsomorphisms_forget₂ [HasForget₂ C D] [ReflectsIsomorphisms (forget C)] :
    ReflectsIsomorphisms (forget₂ C D) :=
  {
    reflects := fun X Y f i => by
      skip
      haveI i' : is_iso ((forget D).map ((forget₂ C D).map f)) := functor.map_is_iso (forget D) _
      haveI : is_iso ((forget C).map f) :=
        by
        have := has_forget₂.forget_comp
        dsimp at this
        rw [← this]
        exact i'
      apply is_iso_of_reflects_iso f (forget C) }
#align category_theory.reflects_isomorphisms_forget₂ CategoryTheory.reflectsIsomorphisms_forget₂

end CategoryTheory

