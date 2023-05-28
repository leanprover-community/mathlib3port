/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module category_theory.category.ulift
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Basic
import Mathbin.CategoryTheory.Equivalence
import Mathbin.CategoryTheory.EqToHom

/-!
# Basic API for ulift

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains a very basic API for working with the categorical
instance on `ulift C` where `C` is a type with a category instance.

1. `category_theory.ulift.up` is the functorial version of the usual `ulift.up`.
2. `category_theory.ulift.down` is the functorial version of the usual `ulift.down`.
3. `category_theory.ulift.equivalence` is the categorical equivalence between
  `C` and `ulift C`.

# ulift_hom

Given a type `C : Type u`, `ulift_hom.{w} C` is just an alias for `C`.
If we have `category.{v} C`, then `ulift_hom.{w} C` is endowed with a category instance
whose morphisms are obtained by applying `ulift.{w}` to the morphisms from `C`.

This is a category equivalent to `C`. The forward direction of the equivalence is `ulift_hom.up`,
the backward direction is `ulift_hom.donw` and the equivalence is `ulift_hom.equiv`.

# as_small

This file also contains a construction which takes a type `C : Type u` with a
category instance `category.{v} C` and makes a small category
`as_small.{w} C : Type (max w v u)` equivalent to `C`.

The forward direction of the equivalence, `C ⥤ as_small C`, is denoted `as_small.up`
and the backward direction is `as_small.down`. The equivalence itself is `as_small.equiv`.
-/


universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

#print CategoryTheory.ULift.upFunctor /-
/-- The functorial version of `ulift.up`. -/
@[simps]
def ULift.upFunctor : C ⥤ ULift.{u₂} C where
  obj := ULift.up
  map X Y f := f
#align category_theory.ulift.up_functor CategoryTheory.ULift.upFunctor
-/

#print CategoryTheory.ULift.downFunctor /-
/-- The functorial version of `ulift.down`. -/
@[simps]
def ULift.downFunctor : ULift.{u₂} C ⥤ C
    where
  obj := ULift.down
  map X Y f := f
#align category_theory.ulift.down_functor CategoryTheory.ULift.downFunctor
-/

/- warning: category_theory.ulift.equivalence -> CategoryTheory.ULift.equivalence is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, u1, u2, max u2 u3} C _inst_1 (ULift.{u3, u2} C) (CategoryTheory.uliftCategory.{u1, u2, u3} C _inst_1)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, u1, u2, max u3 u2} C (ULift.{u3, u2} C) _inst_1 (CategoryTheory.uliftCategory.{u1, u2, u3} C _inst_1)
Case conversion may be inaccurate. Consider using '#align category_theory.ulift.equivalence CategoryTheory.ULift.equivalenceₓ'. -/
/-- The categorical equivalence between `C` and `ulift C`. -/
@[simps]
def ULift.equivalence : C ≌ ULift.{u₂} C
    where
  Functor := ULift.upFunctor
  inverse := ULift.downFunctor
  unitIso :=
    { Hom := 𝟙 _
      inv := 𝟙 _ }
  counitIso :=
    { Hom :=
        { app := fun X => 𝟙 _
          naturality' := fun X Y f => by change f ≫ 𝟙 _ = 𝟙 _ ≫ f; simp }
      inv :=
        { app := fun X => 𝟙 _
          naturality' := fun X Y f => by change f ≫ 𝟙 _ = 𝟙 _ ≫ f; simp }
      hom_inv_id' := by ext; change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
      inv_hom_id' := by ext; change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp }
  functor_unitIso_comp' X := by change 𝟙 X ≫ 𝟙 X = 𝟙 X; simp
#align category_theory.ulift.equivalence CategoryTheory.ULift.equivalence

section UliftHom

#print CategoryTheory.ULiftHom /-
/-- `ulift_hom.{w} C` is an alias for `C`, which is endowed with a category instance
  whose morphisms are obtained by applying `ulift.{w}` to the morphisms from `C`.
-/
def ULiftHom.{w, u} (C : Type u) :=
  C
#align category_theory.ulift_hom CategoryTheory.ULiftHom
-/

instance {C} [Inhabited C] : Inhabited (ULiftHom C) :=
  ⟨(Inhabited.default C : C)⟩

#print CategoryTheory.ULiftHom.objDown /-
/-- The obvious function `ulift_hom C → C`. -/
def ULiftHom.objDown {C} (A : ULiftHom C) : C :=
  A
#align category_theory.ulift_hom.obj_down CategoryTheory.ULiftHom.objDown
-/

#print CategoryTheory.ULiftHom.objUp /-
/-- The obvious function `C → ulift_hom C`. -/
def ULiftHom.objUp {C} (A : C) : ULiftHom C :=
  A
#align category_theory.ulift_hom.obj_up CategoryTheory.ULiftHom.objUp
-/

/- warning: category_theory.obj_down_obj_up -> CategoryTheory.objDown_objUp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} (A : C), Eq.{succ u1} C (CategoryTheory.ULiftHom.objDown.{u1, u2} C (CategoryTheory.ULiftHom.objUp.{u1, u2} C A)) A
but is expected to have type
  forall {C : Type.{u2}} (A : C), Eq.{succ u2} C (CategoryTheory.ULiftHom.objDown.{u2, u1} C (CategoryTheory.ULiftHom.objUp.{u2, u1} C A)) A
Case conversion may be inaccurate. Consider using '#align category_theory.obj_down_obj_up CategoryTheory.objDown_objUpₓ'. -/
@[simp]
theorem objDown_objUp {C} (A : C) : (ULiftHom.objUp A).objDown = A :=
  rfl
#align category_theory.obj_down_obj_up CategoryTheory.objDown_objUp

/- warning: category_theory.obj_up_obj_down -> CategoryTheory.objUp_objDown is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} (A : CategoryTheory.ULiftHom.{u2, u1} C), Eq.{succ u1} (CategoryTheory.ULiftHom.{u2, u1} C) (CategoryTheory.ULiftHom.objUp.{u1, u2} C (CategoryTheory.ULiftHom.objDown.{u1, u2} C A)) A
but is expected to have type
  forall {C : Type.{u2}} (A : CategoryTheory.ULiftHom.{u1, u2} C), Eq.{succ u2} (CategoryTheory.ULiftHom.{u1, u2} C) (CategoryTheory.ULiftHom.objUp.{u2, u1} C (CategoryTheory.ULiftHom.objDown.{u2, u1} C A)) A
Case conversion may be inaccurate. Consider using '#align category_theory.obj_up_obj_down CategoryTheory.objUp_objDownₓ'. -/
@[simp]
theorem objUp_objDown {C} (A : ULiftHom C) : ULiftHom.objUp A.objDown = A :=
  rfl
#align category_theory.obj_up_obj_down CategoryTheory.objUp_objDown

instance : Category.{max v₂ v₁} (ULiftHom.{v₂} C)
    where
  Hom A B := ULift.{v₂} <| A.objDown ⟶ B.objDown
  id A := ⟨𝟙 _⟩
  comp A B C f g := ⟨f.down ≫ g.down⟩

#print CategoryTheory.ULiftHom.up /-
/-- One half of the quivalence between `C` and `ulift_hom C`. -/
@[simps]
def ULiftHom.up : C ⥤ ULiftHom C where
  obj := ULiftHom.objUp
  map X Y f := ⟨f⟩
#align category_theory.ulift_hom.up CategoryTheory.ULiftHom.up
-/

#print CategoryTheory.ULiftHom.down /-
/-- One half of the quivalence between `C` and `ulift_hom C`. -/
@[simps]
def ULiftHom.down : ULiftHom C ⥤ C where
  obj := ULiftHom.objDown
  map X Y f := f.down
#align category_theory.ulift_hom.down CategoryTheory.ULiftHom.down
-/

/- warning: category_theory.ulift_hom.equiv -> CategoryTheory.ULiftHom.equiv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, max u3 u1, u2, u2} C _inst_1 (CategoryTheory.ULiftHom.{u3, u2} C) (CategoryTheory.ULiftHom.category.{u1, u3, u2} C _inst_1)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, max u1 u3, u2, u2} C (CategoryTheory.ULiftHom.{u3, u2} C) _inst_1 (CategoryTheory.ULiftHom.category.{u1, u3, u2} C _inst_1)
Case conversion may be inaccurate. Consider using '#align category_theory.ulift_hom.equiv CategoryTheory.ULiftHom.equivₓ'. -/
/-- The equivalence between `C` and `ulift_hom C`. -/
def ULiftHom.equiv : C ≌ ULiftHom C
    where
  Functor := ULiftHom.up
  inverse := ULiftHom.down
  unitIso := NatIso.ofComponents (fun A => eqToIso rfl) (by tidy)
  counitIso := NatIso.ofComponents (fun A => eqToIso rfl) (by tidy)
#align category_theory.ulift_hom.equiv CategoryTheory.ULiftHom.equiv

end UliftHom

#print CategoryTheory.AsSmall /-
/-- `as_small C` is a small category equivalent to `C`.
  More specifically, if `C : Type u` is endowed with `category.{v} C`, then
  `as_small.{w} C : Type (max w v u)` is endowed with an instance of a small category.

  The objects and morphisms of `as_small C` are defined by applying `ulift` to the
  objects and morphisms of `C`.

  Note: We require a category instance for this definition in order to have direct
  access to the universe level `v`.
-/
@[nolint unused_arguments]
def AsSmall.{w, v, u} (C : Type u) [Category.{v} C] :=
  ULift.{max w v} C
#align category_theory.as_small CategoryTheory.AsSmall
-/

instance : SmallCategory (AsSmall.{w₁} C)
    where
  Hom X Y := ULift.{max w₁ u₁} <| X.down ⟶ Y.down
  id X := ⟨𝟙 _⟩
  comp X Y Z f g := ⟨f.down ≫ g.down⟩

#print CategoryTheory.AsSmall.up /-
/-- One half of the equivalence between `C` and `as_small C`. -/
@[simps]
def AsSmall.up : C ⥤ AsSmall C where
  obj X := ⟨X⟩
  map X Y f := ⟨f⟩
#align category_theory.as_small.up CategoryTheory.AsSmall.up
-/

#print CategoryTheory.AsSmall.down /-
/-- One half of the equivalence between `C` and `as_small C`. -/
@[simps]
def AsSmall.down : AsSmall C ⥤ C where
  obj X := X.down
  map X Y f := f.down
#align category_theory.as_small.down CategoryTheory.AsSmall.down
-/

/- warning: category_theory.as_small.equiv -> CategoryTheory.AsSmall.equiv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, max u2 u3 u1, u2, max u2 u3 u1} C _inst_1 (CategoryTheory.AsSmall.{u3, u1, u2} C _inst_1) (CategoryTheory.AsSmall.smallCategory.{u3, u1, u2} C _inst_1)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, max (max u2 u1) u3, u2, max (max u2 u1) u3} C (CategoryTheory.AsSmall.{u3, u1, u2} C _inst_1) _inst_1 (CategoryTheory.instSmallCategoryAsSmall.{u3, u1, u2} C _inst_1)
Case conversion may be inaccurate. Consider using '#align category_theory.as_small.equiv CategoryTheory.AsSmall.equivₓ'. -/
/-- The equivalence between `C` and `as_small C`. -/
@[simps]
def AsSmall.equiv : C ≌ AsSmall C where
  Functor := AsSmall.up
  inverse := AsSmall.down
  unitIso := NatIso.ofComponents (fun X => eqToIso rfl) (by tidy)
  counitIso := NatIso.ofComponents (fun X => eqToIso <| by ext; rfl) (by tidy)
#align category_theory.as_small.equiv CategoryTheory.AsSmall.equiv

instance [Inhabited C] : Inhabited (AsSmall C) :=
  ⟨⟨Inhabited.default _⟩⟩

/- warning: category_theory.ulift_hom_ulift_category.equiv -> CategoryTheory.ULiftHomULiftCategory.equiv is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u3, u4} C], CategoryTheory.Equivalence.{u3, max u1 u3, u4, max u4 u2} C _inst_2 (CategoryTheory.ULiftHom.{u1, max u4 u2} (ULift.{u2, u4} C)) (CategoryTheory.ULiftHom.category.{u3, u1, max u4 u2} (ULift.{u2, u4} C) (CategoryTheory.uliftCategory.{u3, u4, u2} C _inst_2))
but is expected to have type
  forall (C : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u3, u4} C], CategoryTheory.Equivalence.{u3, max u3 u1, u4, max u2 u4} C (CategoryTheory.ULiftHom.{u1, max u2 u4} (ULift.{u2, u4} C)) _inst_2 (CategoryTheory.ULiftHom.category.{u3, u1, max u4 u2} (ULift.{u2, u4} C) (CategoryTheory.uliftCategory.{u3, u4, u2} C _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.ulift_hom_ulift_category.equiv CategoryTheory.ULiftHomULiftCategory.equivₓ'. -/
/-- The equivalence between `C` and `ulift_hom (ulift C)`. -/
def ULiftHomULiftCategory.equiv.{v', u', v, u} (C : Type u) [Category.{v} C] :
    C ≌ ULiftHom.{v'} (ULift.{u'} C) :=
  ULift.equivalence.trans ULiftHom.equiv
#align category_theory.ulift_hom_ulift_category.equiv CategoryTheory.ULiftHomULiftCategory.equiv

end CategoryTheory

