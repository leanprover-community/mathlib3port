/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import Mathbin.Algebra.Category.GroupCat.Basic
import Mathbin.GroupTheory.FreeAbelianGroup

/-!
# Adjunctions regarding the category of (abelian) groups

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

namespace AddCommGroupCat

open Classical

/-- The free functor `Type u ⥤ AddCommGroup` sending a type `X` to the
free abelian group with generators `x : X`.
-/
def free : Type u ⥤ AddCommGroupCat where
  obj α := of (FreeAbelianGroup α)
  map X Y := FreeAbelianGroup.map
  map_id' X := AddMonoidHom.ext FreeAbelianGroup.map_id_apply
  map_comp' X Y Z f g := AddMonoidHom.ext FreeAbelianGroup.map_comp_apply

@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = FreeAbelianGroup α :=
  rfl

@[simp]
theorem free_map_coe {α β : Type u} {f : α → β} (x : FreeAbelianGroup α) : (free.map f) x = f <$> x :=
  rfl

/-- The free-forgetful adjunction for abelian groups.
-/
def adj : free ⊣ forget AddCommGroupCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeAbelianGroup.lift.symm,
      hom_equiv_naturality_left_symm' := by
        intros
        ext
        rfl }

instance : IsRightAdjoint (forget AddCommGroupCat.{u}) :=
  ⟨_, adj⟩

/-- As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
example {G H : AddCommGroupCat.{u}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  (mono_iff_injective f).1 (show Mono ((forget AddCommGroupCat.{u}).map f) by infer_instance)

end AddCommGroupCat

namespace GroupCat

/-- The free functor `Type u ⥤ Group` sending a type `X` to the free group with generators `x : X`.
-/
def free : Type u ⥤ GroupCat where
  obj α := of (FreeGroup α)
  map X Y := FreeGroup.map
  map_id' := by
    intros
    ext1
    rfl
  map_comp' := by
    intros
    ext1
    rfl

/-- The free-forgetful adjunction for groups.
-/
def adj : free ⊣ forget GroupCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeGroup.lift.symm,
      hom_equiv_naturality_left_symm' := fun X Y G f g => by
        ext1
        rfl }

instance : IsRightAdjoint (forget GroupCat.{u}) :=
  ⟨_, adj⟩

end GroupCat

section Abelianization

/-- The abelianization functor `Group ⥤ CommGroup` sending a group `G` to its abelianization `Gᵃᵇ`.
 -/
def abelianize : GroupCat.{u} ⥤ CommGroupCat.{u} where
  obj G := { α := Abelianization G, str := by infer_instance }
  map G H f :=
    Abelianization.lift { toFun := fun x => Abelianization.of (f x), map_one' := by simp, map_mul' := by simp }
  map_id' := by
    intros
    simp only [MonoidHom.mk_coe, coe_id]
    ext1
    rfl
  map_comp' := by
    intros
    simp only [coe_comp]
    ext1
    rfl

/-- The abelianization-forgetful adjuction from `Group` to `CommGroup`.-/
def abelianizeAdj : abelianize ⊣ forget₂ CommGroupCat.{u} GroupCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G A => Abelianization.lift.symm,
      hom_equiv_naturality_left_symm' := fun G H A f g => by
        ext1
        rfl }

end Abelianization

/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def MonCat.units : MonCat.{u} ⥤ GroupCat.{u} where
  obj R := GroupCat.of Rˣ
  map R S f := GroupCat.ofHom <| Units.map f
  map_id' X := MonoidHom.ext fun x => Units.ext rfl
  map_comp' X Y Z f g := MonoidHom.ext fun x => Units.ext rfl

/-- The forgetful-units adjunction between `Group` and `Mon`. -/
def GroupCat.forget₂MonAdj : forget₂ GroupCat MonCat ⊣ MonCat.units.{u} where
  homEquiv X Y :=
    { toFun := fun f => MonoidHom.toHomUnits f, invFun := fun f => (Units.coeHom Y).comp f,
      left_inv := fun f => MonoidHom.ext fun _ => rfl, right_inv := fun f => MonoidHom.ext fun _ => Units.ext rfl }
  Unit :=
    { app := fun X => { (@toUnits X _).toMonoidHom with },
      naturality' := fun X Y f => MonoidHom.ext fun x => Units.ext rfl }
  counit := { app := fun X => Units.coeHom X, naturality' := fun X Y f => MonoidHom.ext fun x => rfl }
  hom_equiv_unit' X Y f := MonoidHom.ext fun _ => Units.ext rfl
  hom_equiv_counit' X Y f := MonoidHom.ext fun _ => rfl

instance : IsRightAdjoint MonCat.units.{u} :=
  ⟨_, GroupCat.forget₂MonAdj⟩

/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def CommMonCat.units : CommMonCat.{u} ⥤ CommGroupCat.{u} where
  obj R := CommGroupCat.of Rˣ
  map R S f := CommGroupCat.ofHom <| Units.map f
  map_id' X := MonoidHom.ext fun x => Units.ext rfl
  map_comp' X Y Z f g := MonoidHom.ext fun x => Units.ext rfl

/-- The forgetful-units adjunction between `CommGroup` and `CommMon`. -/
def CommGroupCat.forget₂CommMonAdj : forget₂ CommGroupCat CommMonCat ⊣ CommMonCat.units.{u} where
  homEquiv X Y :=
    { toFun := fun f => MonoidHom.toHomUnits f, invFun := fun f => (Units.coeHom Y).comp f,
      left_inv := fun f => MonoidHom.ext fun _ => rfl, right_inv := fun f => MonoidHom.ext fun _ => Units.ext rfl }
  Unit :=
    { app := fun X => { (@toUnits X _).toMonoidHom with },
      naturality' := fun X Y f => MonoidHom.ext fun x => Units.ext rfl }
  counit := { app := fun X => Units.coeHom X, naturality' := fun X Y f => MonoidHom.ext fun x => rfl }
  hom_equiv_unit' X Y f := MonoidHom.ext fun _ => Units.ext rfl
  hom_equiv_counit' X Y f := MonoidHom.ext fun _ => rfl

instance : IsRightAdjoint CommMonCat.units.{u} :=
  ⟨_, CommGroupCat.forget₂CommMonAdj⟩

