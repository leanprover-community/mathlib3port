/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebraic_geometry.sheafed_space
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace.HasColimits
import Mathbin.Topology.Sheaves.Functors

/-!
# Sheafed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/


universe v u

open CategoryTheory

open TopCat

open TopologicalSpace

open Opposite

open CategoryTheory.Limits

open CategoryTheory.Category CategoryTheory.Functor

variable (C : Type u) [Category.{v} C]

attribute [local tidy] tactic.op_induction'

namespace AlgebraicGeometry

#print AlgebraicGeometry.SheafedSpace /-
/-- A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s. -/
structure SheafedSpace extends PresheafedSpace.{v} C where
  IsSheaf : presheaf.IsSheaf
#align algebraic_geometry.SheafedSpace AlgebraicGeometry.SheafedSpace
-/

variable {C}

namespace SheafedSpace

/- warning: algebraic_geometry.SheafedSpace.coe_carrier -> AlgebraicGeometry.SheafedSpace.coeCarrier is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], Coe.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) TopCat.{u1}
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CoeOut.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) TopCat.{u1}
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.coe_carrier AlgebraicGeometry.SheafedSpace.coeCarrierₓ'. -/
instance coeCarrier : Coe (SheafedSpace C) TopCat where coe X := X.carrier
#align algebraic_geometry.SheafedSpace.coe_carrier AlgebraicGeometry.SheafedSpace.coeCarrier

#print AlgebraicGeometry.SheafedSpace.sheaf /-
/-- Extract the `sheaf C (X : Top)` from a `SheafedSpace C`. -/
def sheaf (X : SheafedSpace C) : Sheaf C (X : TopCat.{v}) :=
  ⟨X.Presheaf, X.IsSheaf⟩
#align algebraic_geometry.SheafedSpace.sheaf AlgebraicGeometry.SheafedSpace.sheaf
-/

/- warning: algebraic_geometry.SheafedSpace.as_coe clashes with [anonymous] -> [anonymous]
warning: algebraic_geometry.SheafedSpace.as_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1), Eq.{succ (succ u1)} TopCat.{u1} (AlgebraicGeometry.PresheafedSpace.carrier.{u1, u1, u2} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 X)) ((fun (a : Sort.{max (succ u2) (succ (succ u1))}) (b : Type.{succ u1}) [self : HasLiftT.{max (succ u2) (succ (succ u1)), succ (succ u1)} a b] => self.0) (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) TopCat.{u1} (HasLiftT.mk.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) TopCat.{u1} (CoeTCₓ.coe.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) TopCat.{u1} (coeBase.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) TopCat.{u1} (AlgebraicGeometry.SheafedSpace.coeCarrier.{u1, u2} C _inst_1)))) X)
but is expected to have type
  forall {C : Type.{u1}} {_inst_1 : Type.{u2}}, (Nat -> C -> _inst_1) -> Nat -> (List.{u1} C) -> (List.{u2} _inst_1)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.as_coe [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (X : SheafedSpace.{v} C) : X.carrier = (X : TopCat.{v}) :=
  rfl
#align algebraic_geometry.SheafedSpace.as_coe [anonymous]

#print AlgebraicGeometry.SheafedSpace.mk_coe /-
@[simp]
theorem mk_coe (carrier) (presheaf) (h) :
    (({     carrier
            Presheaf
            IsSheaf := h } : SheafedSpace.{v} C) : TopCat.{v}) = carrier :=
  rfl
#align algebraic_geometry.SheafedSpace.mk_coe AlgebraicGeometry.SheafedSpace.mk_coe
-/

instance (X : SheafedSpace.{v} C) : TopologicalSpace X :=
  X.carrier.str

#print AlgebraicGeometry.SheafedSpace.unit /-
/-- The trivial `unit` valued sheaf on any topological space. -/
def unit (X : TopCat) : SheafedSpace (discrete Unit) :=
  { @PresheafedSpace.const (discrete Unit) _ X ⟨⟨⟩⟩ with IsSheaf := Presheaf.isSheaf_unit _ }
#align algebraic_geometry.SheafedSpace.unit AlgebraicGeometry.SheafedSpace.unit
-/

instance : Inhabited (SheafedSpace (discrete Unit)) :=
  ⟨unit (TopCat.of PEmpty)⟩

instance : Category (SheafedSpace C) :=
  show Category (InducedCategory (PresheafedSpace.{v} C) SheafedSpace.toPresheafedSpace) by
    infer_instance

/- warning: algebraic_geometry.SheafedSpace.forget_to_PresheafedSpace -> AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Functor.{u1, u1, max u2 (succ u1), max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.CategoryTheory.category.{u1, u2} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u1, u2} C _inst_1)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Functor.{u1, u1, max (succ u1) u2, max (succ u1) u2} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.instCategorySheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{u2, u1, u1} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u2, u1, u1} C _inst_1)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.forget_to_PresheafedSpace AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpaceₓ'. -/
/-- Forgetting the sheaf condition is a functor from `SheafedSpace C` to `PresheafedSpace C`. -/
def forgetToPresheafedSpace : SheafedSpace.{v} C ⥤ PresheafedSpace.{v} C :=
  inducedFunctor _ deriving Full, Faithful
#align algebraic_geometry.SheafedSpace.forget_to_PresheafedSpace AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace

/- warning: algebraic_geometry.SheafedSpace.is_PresheafedSpace_iso -> AlgebraicGeometry.SheafedSpace.is_presheafedSpace_iso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1} {Y : AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1} (f : Quiver.Hom.{succ u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.CategoryTheory.category.{u1, u2} C _inst_1))) X Y) [_inst_2 : CategoryTheory.IsIso.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.CategoryTheory.category.{u1, u2} C _inst_1) X Y f], CategoryTheory.IsIso.{u1, max u2 (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 X) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Y) f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1} {Y : AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1} (f : Quiver.Hom.{succ u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.instCategorySheafedSpace.{u1, u2} C _inst_1))) X Y) [_inst_2 : CategoryTheory.IsIso.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.instCategorySheafedSpace.{u1, u2} C _inst_1) X Y f], CategoryTheory.IsIso.{u1, max (succ u1) u2} (AlgebraicGeometry.PresheafedSpace.{u2, u1, u1} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u2, u1, u1} C _inst_1) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 X) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Y) f
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.is_PresheafedSpace_iso AlgebraicGeometry.SheafedSpace.is_presheafedSpace_isoₓ'. -/
instance is_presheafedSpace_iso {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) [IsIso f] :
    @IsIso (PresheafedSpace C) _ _ _ f :=
  SheafedSpace.forgetToPresheafedSpace.map_isIso f
#align algebraic_geometry.SheafedSpace.is_PresheafedSpace_iso AlgebraicGeometry.SheafedSpace.is_presheafedSpace_iso

variable {C}

section

attribute [local simp] id comp

#print AlgebraicGeometry.SheafedSpace.id_base /-
@[simp]
theorem id_base (X : SheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat.{v}) :=
  rfl
#align algebraic_geometry.SheafedSpace.id_base AlgebraicGeometry.SheafedSpace.id_base
-/

/- warning: algebraic_geometry.SheafedSpace.id_c -> AlgebraicGeometry.SheafedSpace.id_c is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.id_c AlgebraicGeometry.SheafedSpace.id_cₓ'. -/
theorem id_c (X : SheafedSpace C) :
    (𝟙 X : X ⟶ X).c = eqToHom (Presheaf.Pushforward.id_eq X.Presheaf).symm :=
  rfl
#align algebraic_geometry.SheafedSpace.id_c AlgebraicGeometry.SheafedSpace.id_c

/- warning: algebraic_geometry.SheafedSpace.id_c_app -> AlgebraicGeometry.SheafedSpace.id_c_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.id_c_app AlgebraicGeometry.SheafedSpace.id_c_appₓ'. -/
@[simp]
theorem id_c_app (X : SheafedSpace C) (U) :
    (𝟙 X : X ⟶ X).c.app U = eqToHom (by induction U using Opposite.rec'; cases U; rfl) := by
  induction U using Opposite.rec'; cases U; simp only [id_c]; dsimp; simp
#align algebraic_geometry.SheafedSpace.id_c_app AlgebraicGeometry.SheafedSpace.id_c_app

/- warning: algebraic_geometry.SheafedSpace.comp_base -> AlgebraicGeometry.SheafedSpace.comp_base is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1} {Y : AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1} {Z : AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1} (f : Quiver.Hom.{succ u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.CategoryTheory.category.{u1, u2} C _inst_1))) X Y) (g : Quiver.Hom.{succ u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.CategoryTheory.category.{u1, u2} C _inst_1))) Y Z), Eq.{succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1})) ((fun (a : Sort.{max (succ u2) (succ (succ u1))}) (b : Type.{succ u1}) [self : HasLiftT.{max (succ u2) (succ (succ u1)), succ (succ u1)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (HasLiftT.mk.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (CoeTCₓ.coe.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (coeBase.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{u1, u1, u2} C _inst_1)))) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 X)) ((fun (a : Sort.{max (succ u2) (succ (succ u1))}) (b : Type.{succ u1}) [self : HasLiftT.{max (succ u2) (succ (succ u1)), succ (succ u1)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (HasLiftT.mk.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (CoeTCₓ.coe.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (coeBase.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{u1, u1, u2} C _inst_1)))) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Z))) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u1, u1, u2} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 X) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Z) (CategoryTheory.CategoryStruct.comp.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.CategoryTheory.category.{u1, u2} C _inst_1)) X Y Z f g)) (CategoryTheory.CategoryStruct.comp.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1}) ((fun (a : Sort.{max (succ u2) (succ (succ u1))}) (b : Type.{succ u1}) [self : HasLiftT.{max (succ u2) (succ (succ u1)), succ (succ u1)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (HasLiftT.mk.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (CoeTCₓ.coe.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (coeBase.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{u1, u1, u2} C _inst_1)))) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 X)) ((fun (a : Sort.{max (succ u2) (succ (succ u1))}) (b : Type.{succ u1}) [self : HasLiftT.{max (succ u2) (succ (succ u1)), succ (succ u1)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (HasLiftT.mk.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (CoeTCₓ.coe.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (coeBase.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{u1, u1, u2} C _inst_1)))) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Y)) ((fun (a : Sort.{max (succ u2) (succ (succ u1))}) (b : Type.{succ u1}) [self : HasLiftT.{max (succ u2) (succ (succ u1)), succ (succ u1)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (HasLiftT.mk.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (CoeTCₓ.coe.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (coeBase.{max (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) TopCat.{u1} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{u1, u1, u2} C _inst_1)))) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Z)) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u1, u1, u2} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 X) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Y) f) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u1, u1, u2} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Y) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Z) g))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1} {Y : AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1} {Z : AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1} (f : Quiver.Hom.{succ u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.instCategorySheafedSpace.{u1, u2} C _inst_1))) X Y) (g : Quiver.Hom.{succ u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.instCategorySheafedSpace.{u1, u2} C _inst_1))) Y Z), Eq.{succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) (AlgebraicGeometry.PresheafedSpace.carrier.{u2, u1, u1} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.carrier.{u2, u1, u1} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Z))) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u2, u1, u1} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 X) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Z) (CategoryTheory.CategoryStruct.comp.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.instCategorySheafedSpace.{u1, u2} C _inst_1)) X Y Z f g)) (CategoryTheory.CategoryStruct.comp.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1}) (AlgebraicGeometry.PresheafedSpace.carrier.{u2, u1, u1} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.carrier.{u2, u1, u1} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Y)) (AlgebraicGeometry.PresheafedSpace.carrier.{u2, u1, u1} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Z)) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u2, u1, u1} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 X) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Y) f) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u2, u1, u1} C _inst_1 (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Y) (AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u1, u2} C _inst_1 Z) g))
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.comp_base AlgebraicGeometry.SheafedSpace.comp_baseₓ'. -/
@[simp]
theorem comp_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl
#align algebraic_geometry.SheafedSpace.comp_base AlgebraicGeometry.SheafedSpace.comp_base

/- warning: algebraic_geometry.SheafedSpace.comp_c_app -> AlgebraicGeometry.SheafedSpace.comp_c_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.comp_c_app AlgebraicGeometry.SheafedSpace.comp_c_appₓ'. -/
@[simp]
theorem comp_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl
#align algebraic_geometry.SheafedSpace.comp_c_app AlgebraicGeometry.SheafedSpace.comp_c_app

/- warning: algebraic_geometry.SheafedSpace.comp_c_app' -> AlgebraicGeometry.SheafedSpace.comp_c_app' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.comp_c_app' AlgebraicGeometry.SheafedSpace.comp_c_app'ₓ'. -/
theorem comp_c_app' {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app (op U) = β.c.app (op U) ≫ α.c.app (op ((Opens.map β.base).obj U)) :=
  rfl
#align algebraic_geometry.SheafedSpace.comp_c_app' AlgebraicGeometry.SheafedSpace.comp_c_app'

/- warning: algebraic_geometry.SheafedSpace.congr_app -> AlgebraicGeometry.SheafedSpace.congr_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.congr_app AlgebraicGeometry.SheafedSpace.congr_appₓ'. -/
theorem congr_app {X Y : SheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.Presheaf.map (eqToHom (by subst h)) :=
  PresheafedSpace.congr_app h U
#align algebraic_geometry.SheafedSpace.congr_app AlgebraicGeometry.SheafedSpace.congr_app

variable (C)

/- warning: algebraic_geometry.SheafedSpace.forget -> AlgebraicGeometry.SheafedSpace.forget is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Functor.{u1, u1, max u2 (succ u1), succ u1} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.CategoryTheory.category.{u1, u2} C _inst_1) TopCat.{u1} TopCat.largeCategory.{u1}
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Functor.{u1, u1, max u2 (succ u1), succ u1} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.instCategorySheafedSpace.{u1, u2} C _inst_1) TopCat.{u1} instTopCatLargeCategory.{u1}
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.forget AlgebraicGeometry.SheafedSpace.forgetₓ'. -/
/-- The forgetful functor from `SheafedSpace` to `Top`. -/
def forget : SheafedSpace C ⥤ TopCat
    where
  obj X := (X : TopCat.{v})
  map X Y f := f.base
#align algebraic_geometry.SheafedSpace.forget AlgebraicGeometry.SheafedSpace.forget

end

open TopCat.Presheaf

/- warning: algebraic_geometry.SheafedSpace.restrict -> AlgebraicGeometry.SheafedSpace.restrict is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.restrict AlgebraicGeometry.SheafedSpace.restrictₓ'. -/
/-- The restriction of a sheafed space along an open embedding into the space.
-/
def restrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) :
    SheafedSpace C :=
  { X.toPresheafedSpace.restrict h with IsSheaf := isSheaf_of_openEmbedding h X.IsSheaf }
#align algebraic_geometry.SheafedSpace.restrict AlgebraicGeometry.SheafedSpace.restrict

/- warning: algebraic_geometry.SheafedSpace.restrict_top_iso -> AlgebraicGeometry.SheafedSpace.restrictTopIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.restrict_top_iso AlgebraicGeometry.SheafedSpace.restrictTopIsoₓ'. -/
/-- The restriction of a sheafed space `X` to the top subspace is isomorphic to `X` itself.
-/
def restrictTopIso (X : SheafedSpace C) : X.restrict (Opens.openEmbedding ⊤) ≅ X :=
  forgetToPresheafedSpace.preimageIso X.toPresheafedSpace.restrictTopIso
#align algebraic_geometry.SheafedSpace.restrict_top_iso AlgebraicGeometry.SheafedSpace.restrictTopIso

/- warning: algebraic_geometry.SheafedSpace.Γ -> AlgebraicGeometry.SheafedSpace.Γ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Functor.{u1, u1, max u2 (succ u1), u2} (Opposite.{succ (max u2 (succ u1))} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.CategoryTheory.category.{u1, u2} C _inst_1)) C _inst_1
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Functor.{u1, u1, max u2 (succ u1), u2} (Opposite.{max (succ u2) (succ (succ u1))} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.instCategorySheafedSpace.{u1, u2} C _inst_1)) C _inst_1
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.Γ AlgebraicGeometry.SheafedSpace.Γₓ'. -/
/-- The global sections, notated Gamma.
-/
def Γ : (SheafedSpace C)ᵒᵖ ⥤ C :=
  forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ
#align algebraic_geometry.SheafedSpace.Γ AlgebraicGeometry.SheafedSpace.Γ

/- warning: algebraic_geometry.SheafedSpace.Γ_def -> AlgebraicGeometry.SheafedSpace.Γ_def is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], Eq.{succ (max u1 u2 (succ u1))} (CategoryTheory.Functor.{u1, u1, max u2 (succ u1), u2} (Opposite.{succ (max u2 (succ u1))} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.CategoryTheory.category.{u1, u2} C _inst_1)) C _inst_1) (AlgebraicGeometry.SheafedSpace.Γ.{u1, u2} C _inst_1) (CategoryTheory.Functor.comp.{u1, u1, u1, max u2 (succ u1), max u2 (succ u1), u2} (Opposite.{succ (max u2 (succ u1))} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.CategoryTheory.category.{u1, u2} C _inst_1)) (Opposite.{succ (max u2 (succ u1))} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u2 (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u1, u2} C _inst_1)) C _inst_1 (CategoryTheory.Functor.op.{u1, u1, max u2 (succ u1), max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.CategoryTheory.category.{u1, u2} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace.{u1, u2} C _inst_1)) (AlgebraicGeometry.PresheafedSpace.Γ.{u1, u2} C _inst_1))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], Eq.{max (succ u2) (succ (succ u1))} (CategoryTheory.Functor.{u1, u1, max u2 (succ u1), u2} (Opposite.{max (succ u2) (succ (succ u1))} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.instCategorySheafedSpace.{u1, u2} C _inst_1)) C _inst_1) (AlgebraicGeometry.SheafedSpace.Γ.{u1, u2} C _inst_1) (CategoryTheory.Functor.comp.{u1, u1, u1, max u2 (succ u1), max u2 (succ u1), u2} (Opposite.{succ (max u2 (succ u1))} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.instCategorySheafedSpace.{u1, u2} C _inst_1)) (Opposite.{succ (max u2 (succ u1))} (AlgebraicGeometry.PresheafedSpace.{u2, u1, u1} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u2 (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u2, u1, u1} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u2, u1, u1} C _inst_1)) C _inst_1 (CategoryTheory.Functor.op.{u1, u1, max u2 (succ u1), max u2 (succ u1)} (AlgebraicGeometry.SheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.SheafedSpace.instCategorySheafedSpace.{u1, u2} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{u2, u1, u1} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u2, u1, u1} C _inst_1) (AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace.{u1, u2} C _inst_1)) (AlgebraicGeometry.PresheafedSpace.Γ.{u2, u1, u1} C _inst_1))
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.Γ_def AlgebraicGeometry.SheafedSpace.Γ_defₓ'. -/
theorem Γ_def : (Γ : _ ⥤ C) = forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ :=
  rfl
#align algebraic_geometry.SheafedSpace.Γ_def AlgebraicGeometry.SheafedSpace.Γ_def

/- warning: algebraic_geometry.SheafedSpace.Γ_obj -> AlgebraicGeometry.SheafedSpace.Γ_obj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.Γ_obj AlgebraicGeometry.SheafedSpace.Γ_objₓ'. -/
@[simp]
theorem Γ_obj (X : (SheafedSpace C)ᵒᵖ) : Γ.obj X = (unop X).Presheaf.obj (op ⊤) :=
  rfl
#align algebraic_geometry.SheafedSpace.Γ_obj AlgebraicGeometry.SheafedSpace.Γ_obj

/- warning: algebraic_geometry.SheafedSpace.Γ_obj_op -> AlgebraicGeometry.SheafedSpace.Γ_obj_op is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.Γ_obj_op AlgebraicGeometry.SheafedSpace.Γ_obj_opₓ'. -/
theorem Γ_obj_op (X : SheafedSpace C) : Γ.obj (op X) = X.Presheaf.obj (op ⊤) :=
  rfl
#align algebraic_geometry.SheafedSpace.Γ_obj_op AlgebraicGeometry.SheafedSpace.Γ_obj_op

/- warning: algebraic_geometry.SheafedSpace.Γ_map -> AlgebraicGeometry.SheafedSpace.Γ_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.Γ_map AlgebraicGeometry.SheafedSpace.Γ_mapₓ'. -/
@[simp]
theorem Γ_map {X Y : (SheafedSpace C)ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.SheafedSpace.Γ_map AlgebraicGeometry.SheafedSpace.Γ_map

/- warning: algebraic_geometry.SheafedSpace.Γ_map_op -> AlgebraicGeometry.SheafedSpace.Γ_map_op is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.SheafedSpace.Γ_map_op AlgebraicGeometry.SheafedSpace.Γ_map_opₓ'. -/
theorem Γ_map_op {X Y : SheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.SheafedSpace.Γ_map_op AlgebraicGeometry.SheafedSpace.Γ_map_op

noncomputable instance [HasLimits C] :
    CreatesColimits (forgetToPresheafedSpace : SheafedSpace C ⥤ _) :=
  ⟨fun J hJ =>
    ⟨fun K =>
      creates_colimit_of_fully_faithful_of_iso
        ⟨(PresheafedSpace.colimit_cocone (K ⋙ forget_to_PresheafedSpace)).pt,
          limit_is_sheaf _ fun j => sheaf.pushforward_sheaf_of_sheaf _ (K.obj (unop j)).2⟩
        (colimit.iso_colimit_cocone ⟨_, PresheafedSpace.colimit_cocone_is_colimit _⟩).symm⟩⟩

instance [HasLimits C] : HasColimits (SheafedSpace C) :=
  has_colimits_of_has_colimits_creates_colimits forgetToPresheafedSpace

noncomputable instance [HasLimits C] : PreservesColimits (forget C) :=
  Limits.compPreservesColimits forgetToPresheafedSpace (PresheafedSpace.forget C)

end SheafedSpace

end AlgebraicGeometry

