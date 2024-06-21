/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import Algebra.Category.Grp.Basic
import GroupTheory.FreeAbelianGroup

#align_import algebra.category.Group.adjunctions from "leanprover-community/mathlib"@"1b089e3bdc3ce6b39cd472543474a0a137128c6c"

/-!
# Adjunctions regarding the category of (abelian) groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains construction of basic adjunctions concerning the category of groups and the
category of abelian groups.

## Main definitions

* `AddCommGroup.free`: constructs the functor associating to a type `X` the free abelian group with
  generators `x : X`.
* `Group.free`: constructs the functor associating to a type `X` the free group with
  generators `x : X`.
* `abelianize`: constructs the functor which associates to a group `G` its abelianization `Gᵃᵇ`.

## Main statements

* `AddCommGroup.adj`: proves that `AddCommGroup.free` is the left adjoint of the forgetful functor
  from abelian groups to types.
* `Group.adj`: proves that `Group.free` is the left adjoint of the forgetful functor from groups to
  types.
* `abelianize_adj`: proves that `abelianize` is left adjoint to the forgetful functor from
  abelian groups to groups.
-/


noncomputable section

universe u

open CategoryTheory

namespace AddCommGrp

open scoped Classical

#print AddCommGrp.free /-
/-- The free functor `Type u ⥤ AddCommGroup` sending a type `X` to the
free abelian group with generators `x : X`.
-/
def free : Type u ⥤ AddCommGrp
    where
  obj α := of (FreeAbelianGroup α)
  map X Y := FreeAbelianGroup.map
  map_id' X := AddMonoidHom.ext FreeAbelianGroup.map_id_apply
  map_comp' X Y Z f g := AddMonoidHom.ext FreeAbelianGroup.map_comp_apply
#align AddCommGroup.free AddCommGrp.free
-/

#print AddCommGrp.free_obj_coe /-
@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = FreeAbelianGroup α :=
  rfl
#align AddCommGroup.free_obj_coe AddCommGrp.free_obj_coe
-/

#print AddCommGrp.free_map_coe /-
@[simp]
theorem free_map_coe {α β : Type u} {f : α → β} (x : FreeAbelianGroup α) :
    (free.map f) x = f <$> x :=
  rfl
#align AddCommGroup.free_map_coe AddCommGrp.free_map_coe
-/

#print AddCommGrp.adj /-
/-- The free-forgetful adjunction for abelian groups.
-/
def adj : free ⊣ forget AddCommGrp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeAbelianGroup.lift.symm
      homEquiv_naturality_left_symm := by intros; ext; rfl }
#align AddCommGroup.adj AddCommGrp.adj
-/

instance : CategoryTheory.Functor.IsRightAdjoint (forget AddCommGrp.{u}) :=
  ⟨_, adj⟩

/-- As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
example {G H : AddCommGrp.{u}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  (mono_iff_injective f).1 (show Mono ((forget AddCommGrp.{u}).map f) by infer_instance)

end AddCommGrp

namespace Grp

#print Grp.free /-
/-- The free functor `Type u ⥤ Group` sending a type `X` to the free group with generators `x : X`.
-/
def free : Type u ⥤ Grp where
  obj α := of (FreeGroup α)
  map X Y := FreeGroup.map
  map_id' := by intros; ext1; rfl
  map_comp' := by intros; ext1; rfl
#align Group.free Grp.free
-/

#print Grp.adj /-
/-- The free-forgetful adjunction for groups.
-/
def adj : free ⊣ forget Grp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeGroup.lift.symm
      homEquiv_naturality_left_symm := fun X Y G f g => by ext1; rfl }
#align Group.adj Grp.adj
-/

instance : CategoryTheory.Functor.IsRightAdjoint (forget Grp.{u}) :=
  ⟨_, adj⟩

end Grp

section Abelianization

#print Grp.abelianize /-
/-- The abelianization functor `Group ⥤ CommGroup` sending a group `G` to its abelianization `Gᵃᵇ`.
 -/
def Grp.abelianize : Grp.{u} ⥤ CommGrp.{u}
    where
  obj G :=
    { α := Abelianization G
      str := by infer_instance }
  map G H f :=
    Abelianization.lift
      { toFun := fun x => Abelianization.of (f x)
        map_one' := by simp
        map_mul' := by simp }
  map_id' := by intros; simp only [MonoidHom.mk_coe, coe_id]; ext1; rfl
  map_comp' := by intros; simp only [coe_comp]; ext1; rfl
#align abelianize Grp.abelianize
-/

#print Grp.abelianizeAdj /-
/-- The abelianization-forgetful adjuction from `Group` to `CommGroup`.-/
def Grp.abelianizeAdj : Grp.abelianize ⊣ forget₂ CommGrp.{u} Grp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G A => Abelianization.lift.symm
      homEquiv_naturality_left_symm := fun G H A f g => by ext1; rfl }
#align abelianize_adj Grp.abelianizeAdj
-/

end Abelianization

#print MonCat.units /-
/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def MonCat.units : MonCat.{u} ⥤ Grp.{u}
    where
  obj R := Grp.of Rˣ
  map R S f := Grp.ofHom <| Units.map f
  map_id' X := MonoidHom.ext fun x => Units.ext rfl
  map_comp' X Y Z f g := MonoidHom.ext fun x => Units.ext rfl
#align Mon.units MonCat.units
-/

#print Grp.forget₂MonAdj /-
/-- The forgetful-units adjunction between `Group` and `Mon`. -/
def Grp.forget₂MonAdj : forget₂ Grp MonCat ⊣ MonCat.units.{u}
    where
  homEquiv X Y :=
    { toFun := fun f => MonoidHom.toHomUnits f
      invFun := fun f => (Units.coeHom Y).comp f
      left_inv := fun f => MonoidHom.ext fun _ => rfl
      right_inv := fun f => MonoidHom.ext fun _ => Units.ext rfl }
  Unit :=
    { app := fun X => { (@toUnits X _).toMonoidHom with }
      naturality' := fun X Y f => MonoidHom.ext fun x => Units.ext rfl }
  counit :=
    { app := fun X => Units.coeHom X
      naturality' := fun X Y f => MonoidHom.ext fun x => rfl }
  homEquiv_unit X Y f := MonoidHom.ext fun _ => Units.ext rfl
  homEquiv_counit X Y f := MonoidHom.ext fun _ => rfl
#align Group.forget₂_Mon_adj Grp.forget₂MonAdj
-/

instance : CategoryTheory.Functor.IsRightAdjoint MonCat.units.{u} :=
  ⟨_, Grp.forget₂MonAdj⟩

#print CommMonCat.units /-
/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def CommMonCat.units : CommMonCat.{u} ⥤ CommGrp.{u}
    where
  obj R := CommGrp.of Rˣ
  map R S f := CommGrp.ofHom <| Units.map f
  map_id' X := MonoidHom.ext fun x => Units.ext rfl
  map_comp' X Y Z f g := MonoidHom.ext fun x => Units.ext rfl
#align CommMon.units CommMonCat.units
-/

#print CommGrp.forget₂CommMonAdj /-
/-- The forgetful-units adjunction between `CommGroup` and `CommMon`. -/
def CommGrp.forget₂CommMonAdj : forget₂ CommGrp CommMonCat ⊣ CommMonCat.units.{u}
    where
  homEquiv X Y :=
    { toFun := fun f => MonoidHom.toHomUnits f
      invFun := fun f => (Units.coeHom Y).comp f
      left_inv := fun f => MonoidHom.ext fun _ => rfl
      right_inv := fun f => MonoidHom.ext fun _ => Units.ext rfl }
  Unit :=
    { app := fun X => { (@toUnits X _).toMonoidHom with }
      naturality' := fun X Y f => MonoidHom.ext fun x => Units.ext rfl }
  counit :=
    { app := fun X => Units.coeHom X
      naturality' := fun X Y f => MonoidHom.ext fun x => rfl }
  homEquiv_unit X Y f := MonoidHom.ext fun _ => Units.ext rfl
  homEquiv_counit X Y f := MonoidHom.ext fun _ => rfl
#align CommGroup.forget₂_CommMon_adj CommGrp.forget₂CommMonAdj
-/

instance : CategoryTheory.Functor.IsRightAdjoint CommMonCat.units.{u} :=
  ⟨_, CommGrp.forget₂CommMonAdj⟩

