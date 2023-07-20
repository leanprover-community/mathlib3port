/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Scott Morrison, Simon Hudon
-/
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.CategoryTheory.Groupoid
import Mathbin.CategoryTheory.Opposites
import Mathbin.GroupTheory.GroupAction.Defs

#align_import category_theory.endomorphism from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
# Endomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Definition and basic properties of endomorphisms and automorphisms of an object in a category.

For each `X : C`, we provide `End X := X ⟶ X` with a monoid structure,
and `Aut X := X ≅ X ` with a group structure.
-/


universe v v' u u'

namespace CategoryTheory

#print CategoryTheory.End /-
/-- Endomorphisms of an object in a category. Arguments order in multiplication agrees with
`function.comp`, not with `category.comp`. -/
def End {C : Type u} [CategoryStruct.{v} C] (X : C) :=
  X ⟶ X
#align category_theory.End CategoryTheory.End
-/

namespace End

section Struct

variable {C : Type u} [CategoryStruct.{v} C] (X : C)

#print CategoryTheory.End.one /-
instance one : One (End X) :=
  ⟨𝟙 X⟩
#align category_theory.End.has_one CategoryTheory.End.one
-/

#print CategoryTheory.End.inhabited /-
instance inhabited : Inhabited (End X) :=
  ⟨𝟙 X⟩
#align category_theory.End.inhabited CategoryTheory.End.inhabited
-/

#print CategoryTheory.End.mul /-
/-- Multiplication of endomorphisms agrees with `function.comp`, not `category_struct.comp`. -/
instance mul : Mul (End X) :=
  ⟨fun x y => y ≫ x⟩
#align category_theory.End.has_mul CategoryTheory.End.mul
-/

variable {X}

#print CategoryTheory.End.of /-
/-- Assist the typechecker by expressing a morphism `X ⟶ X` as a term of `End X`. -/
def of (f : X ⟶ X) : End X :=
  f
#align category_theory.End.of CategoryTheory.End.of
-/

#print CategoryTheory.End.asHom /-
/-- Assist the typechecker by expressing an endomorphism `f : End X` as a term of `X ⟶ X`. -/
def asHom (f : End X) : X ⟶ X :=
  f
#align category_theory.End.as_hom CategoryTheory.End.asHom
-/

#print CategoryTheory.End.one_def /-
@[simp]
theorem one_def : (1 : End X) = 𝟙 X :=
  rfl
#align category_theory.End.one_def CategoryTheory.End.one_def
-/

#print CategoryTheory.End.mul_def /-
@[simp]
theorem mul_def (xs ys : End X) : xs * ys = ys ≫ xs :=
  rfl
#align category_theory.End.mul_def CategoryTheory.End.mul_def
-/

end Struct

#print CategoryTheory.End.monoid /-
/-- Endomorphisms of an object form a monoid -/
instance monoid {C : Type u} [Category.{v} C] {X : C} : Monoid (End X) :=
  { End.mul X, End.one X with
    mul_one := Category.id_comp
    one_mul := Category.comp_id
    mul_assoc := fun x y z => (Category.assoc z y x).symm }
#align category_theory.End.monoid CategoryTheory.End.monoid
-/

section MulAction

variable {C : Type u} [Category.{v} C]

open Opposite

#print CategoryTheory.End.mulActionRight /-
instance mulActionRight {X Y : C} : MulAction (End Y) (X ⟶ Y)
    where
  smul r f := f ≫ r
  one_smul := Category.comp_id
  mul_smul r s f := Eq.symm <| Category.assoc _ _ _
#align category_theory.End.mul_action_right CategoryTheory.End.mulActionRight
-/

#print CategoryTheory.End.mulActionLeft /-
instance mulActionLeft {X : Cᵒᵖ} {Y : C} : MulAction (End X) (unop X ⟶ Y)
    where
  smul r f := r.unop ≫ f
  one_smul := Category.id_comp
  mul_smul r s f := Category.assoc _ _ _
#align category_theory.End.mul_action_left CategoryTheory.End.mulActionLeft
-/

#print CategoryTheory.End.smul_right /-
theorem smul_right {X Y : C} {r : End Y} {f : X ⟶ Y} : r • f = f ≫ r :=
  rfl
#align category_theory.End.smul_right CategoryTheory.End.smul_right
-/

#print CategoryTheory.End.smul_left /-
theorem smul_left {X : Cᵒᵖ} {Y : C} {r : End X} {f : unop X ⟶ Y} : r • f = r.unop ≫ f :=
  rfl
#align category_theory.End.smul_left CategoryTheory.End.smul_left
-/

end MulAction

#print CategoryTheory.End.group /-
/-- In a groupoid, endomorphisms form a group -/
instance group {C : Type u} [Groupoid.{v} C] (X : C) : Group (End X) :=
  { End.monoid with
    mul_left_inv := Groupoid.comp_inv
    inv := Groupoid.inv }
#align category_theory.End.group CategoryTheory.End.group
-/

end End

#print CategoryTheory.isUnit_iff_isIso /-
theorem isUnit_iff_isIso {C : Type u} [Category.{v} C] {X : C} (f : End X) :
    IsUnit (f : End X) ↔ IsIso f :=
  ⟨fun h => { out := ⟨h.Unit.inv, ⟨h.Unit.inv_val, h.Unit.val_inv⟩⟩ }, fun h =>
    ⟨⟨f, inv f, by simp, by simp⟩, rfl⟩⟩
#align category_theory.is_unit_iff_is_iso CategoryTheory.isUnit_iff_isIso
-/

variable {C : Type u} [Category.{v} C] (X : C)

#print CategoryTheory.Aut /-
/-- Automorphisms of an object in a category.

The order of arguments in multiplication agrees with
`function.comp`, not with `category.comp`.
-/
def Aut (X : C) :=
  X ≅ X
#align category_theory.Aut CategoryTheory.Aut
-/

namespace Aut

#print CategoryTheory.Aut.inhabited /-
instance inhabited : Inhabited (Aut X) :=
  ⟨Iso.refl X⟩
#align category_theory.Aut.inhabited CategoryTheory.Aut.inhabited
-/

instance : Group (Aut X) := by
  refine_struct
            { one := iso.refl X
              inv := iso.symm
              mul := flip iso.trans
              div := _
              npow := @npowRec (Aut X) ⟨iso.refl X⟩ ⟨flip iso.trans⟩
              zpow := @zpowRec (Aut X) ⟨iso.refl X⟩ ⟨flip iso.trans⟩ ⟨iso.symm⟩ } <;>
          intros <;>
        try rfl <;>
      ext <;>
    simp [flip, (· * ·), Monoid.mul, MulOneClass.mul, MulOneClass.one, One.one, Monoid.one, Inv.inv]

#print CategoryTheory.Aut.Aut_mul_def /-
theorem Aut_mul_def (f g : Aut X) : f * g = g.trans f :=
  rfl
#align category_theory.Aut.Aut_mul_def CategoryTheory.Aut.Aut_mul_def
-/

#print CategoryTheory.Aut.Aut_inv_def /-
theorem Aut_inv_def (f : Aut X) : f⁻¹ = f.symm :=
  rfl
#align category_theory.Aut.Aut_inv_def CategoryTheory.Aut.Aut_inv_def
-/

#print CategoryTheory.Aut.unitsEndEquivAut /-
/-- Units in the monoid of endomorphisms of an object
are (multiplicatively) equivalent to automorphisms of that object.
-/
def unitsEndEquivAut : (End X)ˣ ≃* Aut X
    where
  toFun f := ⟨f.1, f.2, f.4, f.3⟩
  invFun f := ⟨f.1, f.2, f.4, f.3⟩
  left_inv := fun ⟨f₁, f₂, f₃, f₄⟩ => rfl
  right_inv := fun ⟨f₁, f₂, f₃, f₄⟩ => rfl
  map_mul' f g := by rcases f with ⟨⟩ <;> rcases g with ⟨⟩ <;> rfl
#align category_theory.Aut.units_End_equiv_Aut CategoryTheory.Aut.unitsEndEquivAut
-/

#print CategoryTheory.Aut.autMulEquivOfIso /-
/-- Isomorphisms induce isomorphisms of the automorphism group -/
def autMulEquivOfIso {X Y : C} (h : X ≅ Y) : Aut X ≃* Aut Y
    where
  toFun x := ⟨h.inv ≫ x.Hom ≫ h.Hom, h.inv ≫ x.inv ≫ h.Hom⟩
  invFun y := ⟨h.Hom ≫ y.Hom ≫ h.inv, h.Hom ≫ y.inv ≫ h.inv⟩
  left_inv := by tidy
  right_inv := by tidy
  map_mul' := by simp [Aut_mul_def]
#align category_theory.Aut.Aut_mul_equiv_of_iso CategoryTheory.Aut.autMulEquivOfIso
-/

end Aut

namespace Functor

variable {D : Type u'} [Category.{v'} D] (f : C ⥤ D) (X)

#print CategoryTheory.Functor.mapEnd /-
/-- `f.map` as a monoid hom between endomorphism monoids. -/
@[simps]
def mapEnd : End X →* End (f.obj X)
    where
  toFun := Functor.map f
  map_mul' x y := f.map_comp y x
  map_one' := f.map_id X
#align category_theory.functor.map_End CategoryTheory.Functor.mapEnd
-/

#print CategoryTheory.Functor.mapAut /-
/-- `f.map_iso` as a group hom between automorphism groups. -/
def mapAut : Aut X →* Aut (f.obj X) where
  toFun := f.mapIso
  map_mul' x y := f.mapIso_trans y x
  map_one' := f.mapIso_refl X
#align category_theory.functor.map_Aut CategoryTheory.Functor.mapAut
-/

end Functor

end CategoryTheory

