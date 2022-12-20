/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module category_theory.category.Pointed
! leanprover-community/mathlib commit 550b58538991c8977703fdeb7c9d51a5aa27df11
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.ConcreteCategory.Basic

/-!
# The category of pointed types

This defines `Pointed`, the category of pointed types.

## TODO

* Monoidal structure
* Upgrade `Type_to_Pointed` to an equivalence
-/


open CategoryTheory

universe u

variable {α β : Type _}

/-- The category of pointed types. -/
structure PointedCat : Type (u + 1) where
  x : Type u
  point : X
#align Pointed PointedCat

namespace PointedCat

instance : CoeSort PointedCat (Type _) :=
  ⟨X⟩

attribute [protected] PointedCat.X

/-- Turns a point into a pointed type. -/
def of {X : Type _} (point : X) : PointedCat :=
  ⟨X, point⟩
#align Pointed.of PointedCat.of

@[simp]
theorem coe_of {X : Type _} (point : X) : ↥(of point) = X :=
  rfl
#align Pointed.coe_of PointedCat.coe_of

alias of ← _root_.prod.Pointed

instance : Inhabited PointedCat :=
  ⟨of ((), ())⟩

/-- Morphisms in `Pointed`. -/
@[ext]
protected structure Hom (X Y : PointedCat.{u}) : Type u where
  toFun : X → Y
  map_point : to_fun X.point = Y.point
#align Pointed.hom PointedCat.Hom

namespace Hom

/-- The identity morphism of `X : Pointed`. -/
@[simps]
def id (X : PointedCat) : Hom X X :=
  ⟨id, rfl⟩
#align Pointed.hom.id PointedCat.Hom.id

instance (X : PointedCat) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `Pointed`. -/
@[simps]
def comp {X Y Z : PointedCat.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_point, g.map_point]⟩
#align Pointed.hom.comp PointedCat.Hom.comp

end Hom

instance largeCategory : LargeCategory
      PointedCat where 
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp
  id_comp' _ _ _ := Hom.ext _ _ rfl
  comp_id' _ _ _ := Hom.ext _ _ rfl
  assoc' _ _ _ _ _ _ _ := Hom.ext _ _ rfl
#align Pointed.large_category PointedCat.largeCategory

instance concreteCategory :
    ConcreteCategory
      PointedCat where 
  forget :=
    { obj := PointedCat.X
      map := @Hom.toFun }
  forget_faithful := ⟨@Hom.ext⟩
#align Pointed.concrete_category PointedCat.concreteCategory

/-- Constructs a isomorphism between pointed types from an equivalence that preserves the point
between them. -/
@[simps]
def Iso.mk {α β : PointedCat} (e : α ≃ β) (he : e α.point = β.point) :
    α ≅ β where 
  Hom := ⟨e, he⟩
  inv := ⟨e.symm, e.symm_apply_eq.2 he.symm⟩
  hom_inv_id' := PointedCat.Hom.ext _ _ e.symm_comp_self
  inv_hom_id' := PointedCat.Hom.ext _ _ e.self_comp_symm
#align Pointed.iso.mk PointedCat.Iso.mk

end PointedCat

/-- `option` as a functor from types to pointed types. This is the free functor. -/
@[simps]
def typeToPointed : Type u ⥤
      PointedCat.{u} where 
  obj X := ⟨Option X, none⟩
  map X Y f := ⟨Option.map f, rfl⟩
  map_id' X := PointedCat.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := PointedCat.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Type_to_Pointed typeToPointed

/-- `Type_to_Pointed` is the free functor. -/
def typeToPointedForgetAdjunction : typeToPointed ⊣ forget PointedCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => f.toFun ∘ Option.some
          invFun := fun f => ⟨fun o => o.elim Y.point f, rfl⟩
          left_inv := fun f => by 
            ext
            cases x
            exact f.map_point.symm
            rfl
          right_inv := fun f => funext fun _ => rfl }
      hom_equiv_naturality_left_symm' := fun X' X Y f g => by
        ext
        cases x <;> rfl }
#align Type_to_Pointed_forget_adjunction typeToPointedForgetAdjunction

