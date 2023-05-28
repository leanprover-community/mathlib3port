/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebraic_geometry.presheafed_space
! leanprover-community/mathlib commit 4280f5f32e16755ec7985ce11e189b6cd6ff6735
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sheaves.Presheaf
import Mathbin.CategoryTheory.Adjunction.FullyFaithful

/-!
# Presheafed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/


universe w v u

open CategoryTheory

open TopCat

open TopologicalSpace

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

variable (C : Type u) [Category.{v} C]

attribute [local tidy] tactic.op_induction' tactic.auto_cases_opens

namespace AlgebraicGeometry

/- warning: algebraic_geometry.PresheafedSpace -> AlgebraicGeometry.PresheafedSpace is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u3}) [_inst_1 : CategoryTheory.Category.{u2, u3} C], Sort.{max (succ u3) (succ u2) (succ (succ u1))}
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C], Sort.{max (max (succ u1) (succ u2)) (succ (succ u3))}
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace AlgebraicGeometry.PresheafedSpaceₓ'. -/
/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
structure PresheafedSpace where
  carrier : TopCat.{w}
  Presheaf : carrier.Presheaf C
#align algebraic_geometry.PresheafedSpace AlgebraicGeometry.PresheafedSpace

variable {C}

namespace PresheafedSpace

attribute [protected] presheaf

/- warning: algebraic_geometry.PresheafedSpace.coe_carrier -> AlgebraicGeometry.PresheafedSpace.coeCarrier is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C], Coe.{max (succ u3) (succ u2) (succ (succ u1)), succ (succ u1)} (AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1) TopCat.{u1}
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C], CoeOut.{max (max (succ (succ u3)) (succ u2)) (succ u1), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1) TopCat.{u3}
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.coe_carrier AlgebraicGeometry.PresheafedSpace.coeCarrierₓ'. -/
instance coeCarrier : Coe (PresheafedSpace.{w, v, u} C) TopCat.{w} where coe X := X.carrier
#align algebraic_geometry.PresheafedSpace.coe_carrier AlgebraicGeometry.PresheafedSpace.coeCarrier

@[simp]
theorem as_coe (X : PresheafedSpace.{w, v, u} C) : X.carrier = (X : TopCat.{w}) :=
  rfl
#align algebraic_geometry.PresheafedSpace.as_coe AlgebraicGeometry.PresheafedSpace.as_coe

/- warning: algebraic_geometry.PresheafedSpace.mk_coe -> AlgebraicGeometry.PresheafedSpace.mk_coe is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] (carrier : TopCat.{v}) (presheaf : TopCat.Presheaf.{v, v, u} C _inst_1 carrier), Eq.{succ (succ v)} TopCat.{v} ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) (AlgebraicGeometry.PresheafedSpace.mk.{v, v, u} C _inst_1 carrier presheaf)) carrier
but is expected to have type
  forall {C : Type.{u_3}} [_inst_1 : CategoryTheory.Category.{u_2, u_3} C] (carrier : TopCat.{u_1}) (presheaf : TopCat.Presheaf.{u_1, u_2, u_3} C _inst_1 carrier), Eq.{succ (succ u_1)} TopCat.{u_1} (AlgebraicGeometry.PresheafedSpace.carrier.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.mk.{u_3, u_2, u_1} C _inst_1 carrier presheaf)) carrier
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.mk_coe AlgebraicGeometry.PresheafedSpace.mk_coeₓ'. -/
@[simp]
theorem mk_coe (carrier) (presheaf) :
    (({     carrier
            Presheaf } : PresheafedSpace.{v} C) : TopCat.{v}) = carrier :=
  rfl
#align algebraic_geometry.PresheafedSpace.mk_coe AlgebraicGeometry.PresheafedSpace.mk_coe

instance (X : PresheafedSpace.{v} C) : TopologicalSpace X :=
  X.carrier.str

/- warning: algebraic_geometry.PresheafedSpace.const -> AlgebraicGeometry.PresheafedSpace.const is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], TopCat.{u3} -> C -> (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1)
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C], TopCat.{u3} -> C -> (AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.const AlgebraicGeometry.PresheafedSpace.constₓ'. -/
/-- The constant presheaf on `X` with value `Z`. -/
def const (X : TopCat) (Z : C) : PresheafedSpace C
    where
  carrier := X
  Presheaf :=
    { obj := fun U => Z
      map := fun U V f => 𝟙 Z }
#align algebraic_geometry.PresheafedSpace.const AlgebraicGeometry.PresheafedSpace.const

instance [Inhabited C] : Inhabited (PresheafedSpace C) :=
  ⟨const (TopCat.of PEmpty) default⟩

/- warning: algebraic_geometry.PresheafedSpace.hom -> AlgebraicGeometry.PresheafedSpace.Hom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C], (AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1) -> (AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1) -> Sort.{max (succ u2) (succ u1)}
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C], (AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1) -> (AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1) -> Sort.{max (succ u2) (succ u3)}
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.hom AlgebraicGeometry.PresheafedSpace.Homₓ'. -/
/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
    `f` between the underlying topological spaces, and a (notice contravariant!) map
    from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
structure Hom (X Y : PresheafedSpace.{w, v, u} C) where
  base : (X : TopCat.{w}) ⟶ (Y : TopCat.{w})
  c : Y.Presheaf ⟶ base _* X.Presheaf
#align algebraic_geometry.PresheafedSpace.hom AlgebraicGeometry.PresheafedSpace.Hom

/- warning: algebraic_geometry.PresheafedSpace.ext -> AlgebraicGeometry.PresheafedSpace.Hom.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.ext AlgebraicGeometry.PresheafedSpace.Hom.extₓ'. -/
@[ext]
theorem AlgebraicGeometry.PresheafedSpace.Hom.ext {X Y : PresheafedSpace C} (α β : Hom X Y)
    (w : α.base = β.base) (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β :=
  by
  cases α; cases β
  dsimp [presheaf.pushforward_obj] at *
  tidy
#align algebraic_geometry.PresheafedSpace.ext AlgebraicGeometry.PresheafedSpace.Hom.ext

/- warning: algebraic_geometry.PresheafedSpace.hext -> AlgebraicGeometry.PresheafedSpace.hext is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1} (α : AlgebraicGeometry.PresheafedSpace.Hom.{u3, u1, u2} C _inst_1 X Y) (β : AlgebraicGeometry.PresheafedSpace.Hom.{u3, u1, u2} C _inst_1 X Y), (Eq.{succ u3} (Quiver.Hom.{succ u3, succ u3} TopCat.{u3} (CategoryTheory.CategoryStruct.toQuiver.{u3, succ u3} TopCat.{u3} (CategoryTheory.Category.toCategoryStruct.{u3, succ u3} TopCat.{u3} TopCat.largeCategory.{u3})) ((fun (a : Sort.{max (succ u2) (succ u1) (succ (succ u3))}) (b : Type.{succ u3}) [self : HasLiftT.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (HasLiftT.mk.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (CoeTCₓ.coe.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (coeBase.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{u3, u1, u2} C _inst_1)))) X) ((fun (a : Sort.{max (succ u2) (succ u1) (succ (succ u3))}) (b : Type.{succ u3}) [self : HasLiftT.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (HasLiftT.mk.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (CoeTCₓ.coe.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (coeBase.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{u3, u1, u2} C _inst_1)))) Y)) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u3, u1, u2} C _inst_1 X Y α) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u3, u1, u2} C _inst_1 X Y β)) -> (HEq.{succ (max u3 u1)} (Quiver.Hom.{succ (max u3 u1), max u2 u1 u3} (TopCat.Presheaf.{u3, u1, u2} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u1, u2} C _inst_1 Y)) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u1 u3} (TopCat.Presheaf.{u3, u1, u2} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u1, u2} C _inst_1 Y)) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3} (TopCat.Presheaf.{u3, u1, u2} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u1, u2} C _inst_1 Y)) (TopCat.Presheaf.category.{u1, u3, u2} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u1, u2} C _inst_1 Y)))) (AlgebraicGeometry.PresheafedSpace.presheaf.{u3, u1, u2} C _inst_1 Y) (TopCat.Presheaf.pushforwardObj.{u3, u1, u2} C _inst_1 ((fun (a : Sort.{max (succ u2) (succ u1) (succ (succ u3))}) (b : Type.{succ u3}) [self : HasLiftT.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (HasLiftT.mk.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (CoeTCₓ.coe.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (coeBase.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{u3, u1, u2} C _inst_1)))) X) (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u1, u2} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u3, u1, u2} C _inst_1 X Y α) (AlgebraicGeometry.PresheafedSpace.presheaf.{u3, u1, u2} C _inst_1 X))) (AlgebraicGeometry.PresheafedSpace.Hom.c.{u3, u1, u2} C _inst_1 X Y α) (Quiver.Hom.{succ (max u3 u1), max u2 u1 u3} (TopCat.Presheaf.{u3, u1, u2} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u1, u2} C _inst_1 Y)) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u1 u3} (TopCat.Presheaf.{u3, u1, u2} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u1, u2} C _inst_1 Y)) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3} (TopCat.Presheaf.{u3, u1, u2} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u1, u2} C _inst_1 Y)) (TopCat.Presheaf.category.{u1, u3, u2} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u1, u2} C _inst_1 Y)))) (AlgebraicGeometry.PresheafedSpace.presheaf.{u3, u1, u2} C _inst_1 Y) (TopCat.Presheaf.pushforwardObj.{u3, u1, u2} C _inst_1 ((fun (a : Sort.{max (succ u2) (succ u1) (succ (succ u3))}) (b : Type.{succ u3}) [self : HasLiftT.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (HasLiftT.mk.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (CoeTCₓ.coe.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (coeBase.{max (succ u2) (succ u1) (succ (succ u3)), succ (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1) TopCat.{u3} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{u3, u1, u2} C _inst_1)))) X) (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u1, u2} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u3, u1, u2} C _inst_1 X Y β) (AlgebraicGeometry.PresheafedSpace.presheaf.{u3, u1, u2} C _inst_1 X))) (AlgebraicGeometry.PresheafedSpace.Hom.c.{u3, u1, u2} C _inst_1 X Y β)) -> (Eq.{max (succ u1) (succ u3)} (AlgebraicGeometry.PresheafedSpace.Hom.{u3, u1, u2} C _inst_1 X Y) α β)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {X : AlgebraicGeometry.PresheafedSpace.{u3, u2, u1} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{u3, u2, u1} C _inst_1} (α : AlgebraicGeometry.PresheafedSpace.Hom.{u3, u2, u1} C _inst_1 X Y) (β : AlgebraicGeometry.PresheafedSpace.Hom.{u3, u2, u1} C _inst_1 X Y), (Eq.{succ u1} (Quiver.Hom.{succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 Y)) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u3, u2, u1} C _inst_1 X Y α) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u3, u2, u1} C _inst_1 X Y β)) -> (HEq.{max (succ u2) (succ u1)} (Quiver.Hom.{max (succ u2) (succ u1), max (max u3 u2) u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 Y)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (max u3 u2) u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 Y)) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (max u3 u2) u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 Y)) (TopCat.instCategoryPresheaf.{u1, u2, u3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 Y)))) (AlgebraicGeometry.PresheafedSpace.presheaf.{u3, u2, u1} C _inst_1 Y) (TopCat.Presheaf.pushforwardObj.{u1, u2, u3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u3, u2, u1} C _inst_1 X Y α) (AlgebraicGeometry.PresheafedSpace.presheaf.{u3, u2, u1} C _inst_1 X))) (AlgebraicGeometry.PresheafedSpace.Hom.c.{u3, u2, u1} C _inst_1 X Y α) (Quiver.Hom.{max (succ u2) (succ u1), max (max u3 u2) u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 Y)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (max u3 u2) u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 Y)) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (max u3 u2) u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 Y)) (TopCat.instCategoryPresheaf.{u1, u2, u3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 Y)))) (AlgebraicGeometry.PresheafedSpace.presheaf.{u3, u2, u1} C _inst_1 Y) (TopCat.Presheaf.pushforwardObj.{u1, u2, u3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u2, u1} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u3, u2, u1} C _inst_1 X Y β) (AlgebraicGeometry.PresheafedSpace.presheaf.{u3, u2, u1} C _inst_1 X))) (AlgebraicGeometry.PresheafedSpace.Hom.c.{u3, u2, u1} C _inst_1 X Y β)) -> (Eq.{max (succ u2) (succ u1)} (AlgebraicGeometry.PresheafedSpace.Hom.{u3, u2, u1} C _inst_1 X Y) α β)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.hext AlgebraicGeometry.PresheafedSpace.hextₓ'. -/
-- TODO including `injections` would make tidy work earlier.
theorem hext {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base) (h : HEq α.c β.c) :
    α = β := by cases α; cases β; congr ; exacts[w, h]
#align algebraic_geometry.PresheafedSpace.hext AlgebraicGeometry.PresheafedSpace.hext

/- warning: algebraic_geometry.PresheafedSpace.id -> AlgebraicGeometry.PresheafedSpace.id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (X : AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1), AlgebraicGeometry.PresheafedSpace.Hom.{u1, u2, u3} C _inst_1 X X
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (X : AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1), AlgebraicGeometry.PresheafedSpace.Hom.{u1, u2, u3} C _inst_1 X X
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.id AlgebraicGeometry.PresheafedSpace.idₓ'. -/
/-- The identity morphism of a `PresheafedSpace`. -/
def id (X : PresheafedSpace.{w, v, u} C) : Hom X X
    where
  base := 𝟙 (X : TopCat.{w})
  c := eqToHom (Presheaf.Pushforward.id_eq X.Presheaf).symm
#align algebraic_geometry.PresheafedSpace.id AlgebraicGeometry.PresheafedSpace.id

/- warning: algebraic_geometry.PresheafedSpace.hom_inhabited -> AlgebraicGeometry.PresheafedSpace.homInhabited is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1), Inhabited.{max (succ u1) (succ u3)} (AlgebraicGeometry.PresheafedSpace.Hom.{u3, u1, u2} C _inst_1 X X)
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (X : AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1), Inhabited.{max (succ u3) (succ u2)} (AlgebraicGeometry.PresheafedSpace.Hom.{u1, u2, u3} C _inst_1 X X)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.hom_inhabited AlgebraicGeometry.PresheafedSpace.homInhabitedₓ'. -/
instance homInhabited (X : PresheafedSpace C) : Inhabited (Hom X X) :=
  ⟨id X⟩
#align algebraic_geometry.PresheafedSpace.hom_inhabited AlgebraicGeometry.PresheafedSpace.homInhabited

/- warning: algebraic_geometry.PresheafedSpace.comp -> AlgebraicGeometry.PresheafedSpace.comp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1} {Z : AlgebraicGeometry.PresheafedSpace.{u3, u1, u2} C _inst_1}, (AlgebraicGeometry.PresheafedSpace.Hom.{u3, u1, u2} C _inst_1 X Y) -> (AlgebraicGeometry.PresheafedSpace.Hom.{u3, u1, u2} C _inst_1 Y Z) -> (AlgebraicGeometry.PresheafedSpace.Hom.{u3, u1, u2} C _inst_1 X Z)
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {X : AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1} {Z : AlgebraicGeometry.PresheafedSpace.{u1, u2, u3} C _inst_1}, (AlgebraicGeometry.PresheafedSpace.Hom.{u1, u2, u3} C _inst_1 X Y) -> (AlgebraicGeometry.PresheafedSpace.Hom.{u1, u2, u3} C _inst_1 Y Z) -> (AlgebraicGeometry.PresheafedSpace.Hom.{u1, u2, u3} C _inst_1 X Z)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.comp AlgebraicGeometry.PresheafedSpace.compₓ'. -/
/-- Composition of morphisms of `PresheafedSpace`s. -/
def comp {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z
    where
  base := α.base ≫ β.base
  c := β.c ≫ (Presheaf.pushforward _ β.base).map α.c
#align algebraic_geometry.PresheafedSpace.comp AlgebraicGeometry.PresheafedSpace.comp

/- warning: algebraic_geometry.PresheafedSpace.comp_c -> AlgebraicGeometry.PresheafedSpace.comp_c is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.comp_c AlgebraicGeometry.PresheafedSpace.comp_cₓ'. -/
theorem comp_c {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) :
    (comp α β).c = β.c ≫ (Presheaf.pushforward _ β.base).map α.c :=
  rfl
#align algebraic_geometry.PresheafedSpace.comp_c AlgebraicGeometry.PresheafedSpace.comp_c

variable (C)

section

attribute [local simp] id comp

/- warning: algebraic_geometry.PresheafedSpace.category_of_PresheafedSpaces -> AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u}) [_inst_1 : CategoryTheory.Category.{v, u} C], CategoryTheory.Category.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1)
but is expected to have type
  forall (C : Type.{u_1}) [_inst_1 : CategoryTheory.Category.{u_2, u_1} C], CategoryTheory.Category.{max u_2 u_3, max (max (succ u_3) u_2) u_1} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.category_of_PresheafedSpaces AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpacesₓ'. -/
/- The proofs below can be done by `tidy`, but it is too slow,
   and we don't have a tactic caching mechanism. -/
/-- The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a presheaf map
    from the presheaf on the target to the pushforward of the presheaf on the source. -/
instance categoryOfPresheafedSpaces : Category (PresheafedSpace.{v, v, u} C)
    where
  Hom := Hom
  id := id
  comp X Y Z f g := comp f g
  id_comp' X Y f := by
    ext1
    · rw [comp_c]
      erw [eq_to_hom_map]
      simp only [eq_to_hom_refl, assoc, whisker_right_id']
      erw [comp_id, comp_id]
    apply id_comp
  comp_id' X Y f := by
    ext1
    · rw [comp_c]
      erw [congr_hom (presheaf.id_pushforward _) f.c]
      simp only [comp_id, functor.id_map, eq_to_hom_refl, assoc, whisker_right_id']
      erw [eq_to_hom_trans_assoc]
      simp only [id_comp, eq_to_hom_refl]
      erw [comp_id]
    apply comp_id
  assoc' W X Y Z f g h := by
    ext1
    repeat' rw [comp_c]
    simp only [eq_to_hom_refl, assoc, functor.map_comp, whisker_right_id']
    erw [comp_id]
    congr
    rfl
#align algebraic_geometry.PresheafedSpace.category_of_PresheafedSpaces AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces

end

variable {C}

attribute [local simp] eq_to_hom_map

/- warning: algebraic_geometry.PresheafedSpace.id_base -> AlgebraicGeometry.PresheafedSpace.id_base is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] (X : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1), Eq.{succ v} (Quiver.Hom.{succ v, succ v} TopCat.{v} (CategoryTheory.CategoryStruct.toQuiver.{v, succ v} TopCat.{v} (CategoryTheory.Category.toCategoryStruct.{v, succ v} TopCat.{v} TopCat.largeCategory.{v})) ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X) ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X)) (AlgebraicGeometry.PresheafedSpace.Hom.base.{v, v, u} C _inst_1 X X (CategoryTheory.CategoryStruct.id.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1)) X)) (CategoryTheory.CategoryStruct.id.{v, succ v} TopCat.{v} (CategoryTheory.Category.toCategoryStruct.{v, succ v} TopCat.{v} TopCat.largeCategory.{v}) ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X))
but is expected to have type
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2, u_1} C] (X : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1), Eq.{succ u_3} (Quiver.Hom.{succ u_3, succ u_3} TopCat.{u_3} (CategoryTheory.CategoryStruct.toQuiver.{u_3, succ u_3} TopCat.{u_3} (CategoryTheory.Category.toCategoryStruct.{u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3})) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u_1, u_2, u_3} C _inst_1 X X (CategoryTheory.CategoryStruct.id.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1)) X)) (CategoryTheory.CategoryStruct.id.{u_3, succ u_3} TopCat.{u_3} (CategoryTheory.Category.toCategoryStruct.{u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3}) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X))
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.id_base AlgebraicGeometry.PresheafedSpace.id_baseₓ'. -/
@[simp]
theorem id_base (X : PresheafedSpace.{v, v, u} C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat.{v}) :=
  rfl
#align algebraic_geometry.PresheafedSpace.id_base AlgebraicGeometry.PresheafedSpace.id_base

/- warning: algebraic_geometry.PresheafedSpace.id_c -> AlgebraicGeometry.PresheafedSpace.id_c is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] (X : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1), Eq.{succ v} (Quiver.Hom.{succ v, max u v} (TopCat.Presheaf.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (CategoryTheory.CategoryStruct.toQuiver.{v, max u v} (TopCat.Presheaf.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (CategoryTheory.Category.toCategoryStruct.{v, max u v} (TopCat.Presheaf.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (TopCat.Presheaf.category.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)))) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 X) (TopCat.Presheaf.pushforwardObj.{v, v, u} C _inst_1 ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.Hom.base.{v, v, u} C _inst_1 X X (CategoryTheory.CategoryStruct.id.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1)) X)) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 X))) (AlgebraicGeometry.PresheafedSpace.Hom.c.{v, v, u} C _inst_1 X X (CategoryTheory.CategoryStruct.id.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1)) X)) (CategoryTheory.eqToHom.{v, max u v} (TopCat.Presheaf.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (TopCat.Presheaf.category.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 X) (TopCat.Presheaf.pushforwardObj.{v, v, u} C _inst_1 ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.Hom.base.{v, v, u} C _inst_1 X X (CategoryTheory.CategoryStruct.id.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1)) X)) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 X)) (Eq.symm.{succ (max u v)} (TopCat.Presheaf.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (TopCat.Presheaf.pushforwardObj.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X) (CategoryTheory.CategoryStruct.id.{v, succ v} TopCat.{v} (CategoryTheory.Category.toCategoryStruct.{v, succ v} TopCat.{v} TopCat.largeCategory.{v}) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 X) (TopCat.Presheaf.Pushforward.id_eq.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 X))))
but is expected to have type
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2, u_1} C] (X : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1), Eq.{max (succ u_2) (succ u_3)} (Quiver.Hom.{max (succ u_2) (succ u_3), max (max u_1 u_2) u_3} (TopCat.Presheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X)) (CategoryTheory.CategoryStruct.toQuiver.{max u_2 u_3, max (max u_1 u_2) u_3} (TopCat.Presheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X)) (CategoryTheory.Category.toCategoryStruct.{max u_2 u_3, max (max u_1 u_2) u_3} (TopCat.Presheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X)) (TopCat.instCategoryPresheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X)))) (AlgebraicGeometry.PresheafedSpace.presheaf.{u_1, u_2, u_3} C _inst_1 X) (TopCat.Presheaf.pushforwardObj.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u_1, u_2, u_3} C _inst_1 X X (CategoryTheory.CategoryStruct.id.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1)) X)) (AlgebraicGeometry.PresheafedSpace.presheaf.{u_1, u_2, u_3} C _inst_1 X))) (AlgebraicGeometry.PresheafedSpace.Hom.c.{u_1, u_2, u_3} C _inst_1 X X (CategoryTheory.CategoryStruct.id.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1)) X)) (CategoryTheory.CategoryStruct.id.{max u_2 u_3, max (max u_1 u_2) u_3} (TopCat.Presheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X)) (CategoryTheory.Category.toCategoryStruct.{max u_2 u_3, max (max u_1 u_2) u_3} (TopCat.Presheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X)) (TopCat.instCategoryPresheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X))) (AlgebraicGeometry.PresheafedSpace.presheaf.{u_1, u_2, u_3} C _inst_1 X))
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.id_c AlgebraicGeometry.PresheafedSpace.id_cₓ'. -/
theorem id_c (X : PresheafedSpace.{v, v, u} C) :
    (𝟙 X : X ⟶ X).c = eqToHom (Presheaf.Pushforward.id_eq X.Presheaf).symm :=
  rfl
#align algebraic_geometry.PresheafedSpace.id_c AlgebraicGeometry.PresheafedSpace.id_c

/- warning: algebraic_geometry.PresheafedSpace.id_c_app -> AlgebraicGeometry.PresheafedSpace.id_c_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.id_c_app AlgebraicGeometry.PresheafedSpace.id_c_appₓ'. -/
@[simp]
theorem id_c_app (X : PresheafedSpace.{v, v, u} C) (U) :
    (𝟙 X : X ⟶ X).c.app U =
      X.Presheaf.map (eqToHom (by induction U using Opposite.rec'; cases U; rfl)) :=
  by induction U using Opposite.rec'; cases U; simp only [id_c]; dsimp; simp
#align algebraic_geometry.PresheafedSpace.id_c_app AlgebraicGeometry.PresheafedSpace.id_c_app

/- warning: algebraic_geometry.PresheafedSpace.comp_base -> AlgebraicGeometry.PresheafedSpace.comp_base is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] {X : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} {Z : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} (f : Quiver.Hom.{succ v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1))) X Y) (g : Quiver.Hom.{succ v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1))) Y Z), Eq.{succ v} (Quiver.Hom.{succ v, succ v} TopCat.{v} (CategoryTheory.CategoryStruct.toQuiver.{v, succ v} TopCat.{v} (CategoryTheory.Category.toCategoryStruct.{v, succ v} TopCat.{v} TopCat.largeCategory.{v})) ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X) ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) Z)) (AlgebraicGeometry.PresheafedSpace.Hom.base.{v, v, u} C _inst_1 X Z (CategoryTheory.CategoryStruct.comp.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1)) X Y Z f g)) (CategoryTheory.CategoryStruct.comp.{v, succ v} TopCat.{v} (CategoryTheory.Category.toCategoryStruct.{v, succ v} TopCat.{v} TopCat.largeCategory.{v}) ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X) ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) Y) ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) Z) (AlgebraicGeometry.PresheafedSpace.Hom.base.{v, v, u} C _inst_1 X Y f) (AlgebraicGeometry.PresheafedSpace.Hom.base.{v, v, u} C _inst_1 Y Z g))
but is expected to have type
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2, u_1} C] {X : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1} {Z : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1} (f : Quiver.Hom.{max (succ u_2) (succ u_3), max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1))) X Y) (g : Quiver.Hom.{max (succ u_2) (succ u_3), max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1))) Y Z), Eq.{succ u_3} (Quiver.Hom.{succ u_3, succ u_3} TopCat.{u_3} (CategoryTheory.CategoryStruct.toQuiver.{u_3, succ u_3} TopCat.{u_3} (CategoryTheory.Category.toCategoryStruct.{u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3})) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Z)) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u_1, u_2, u_3} C _inst_1 X Z (CategoryTheory.CategoryStruct.comp.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1)) X Y Z f g)) (CategoryTheory.CategoryStruct.comp.{u_3, succ u_3} TopCat.{u_3} (CategoryTheory.Category.toCategoryStruct.{u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3}) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Z) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u_1, u_2, u_3} C _inst_1 X Y f) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u_1, u_2, u_3} C _inst_1 Y Z g))
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.comp_base AlgebraicGeometry.PresheafedSpace.comp_baseₓ'. -/
@[simp]
theorem comp_base {X Y Z : PresheafedSpace.{v, v, u} C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl
#align algebraic_geometry.PresheafedSpace.comp_base AlgebraicGeometry.PresheafedSpace.comp_base

instance (X Y : PresheafedSpace.{v, v, u} C) : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ⟨fun f => f.base⟩

theorem coe_to_fun_eq {X Y : PresheafedSpace.{v, v, u} C} (f : X ⟶ Y) : (f : X → Y) = f.base :=
  rfl
#align algebraic_geometry.PresheafedSpace.coe_to_fun_eq AlgebraicGeometry.PresheafedSpace.coe_to_fun_eq

/- warning: algebraic_geometry.PresheafedSpace.comp_c_app -> AlgebraicGeometry.PresheafedSpace.comp_c_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.comp_c_app AlgebraicGeometry.PresheafedSpace.comp_c_appₓ'. -/
-- The `reassoc` attribute was added despite the LHS not being a composition of two homs,
-- for the reasons explained in the docstring.
/-- Sometimes rewriting with `comp_c_app` doesn't work because of dependent type issues.
In that case, `erw comp_c_app_assoc` might make progress.
The lemma `comp_c_app_assoc` is also better suited for rewrites in the opposite direction. -/
@[reassoc, simp]
theorem comp_c_app {X Y Z : PresheafedSpace.{v, v, u} C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl
#align algebraic_geometry.PresheafedSpace.comp_c_app AlgebraicGeometry.PresheafedSpace.comp_c_app

/- warning: algebraic_geometry.PresheafedSpace.congr_app -> AlgebraicGeometry.PresheafedSpace.congr_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.congr_app AlgebraicGeometry.PresheafedSpace.congr_appₓ'. -/
theorem congr_app {X Y : PresheafedSpace.{v, v, u} C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.Presheaf.map (eqToHom (by subst h)) := by subst h; dsimp; simp
#align algebraic_geometry.PresheafedSpace.congr_app AlgebraicGeometry.PresheafedSpace.congr_app

section

variable (C)

/- warning: algebraic_geometry.PresheafedSpace.forget -> AlgebraicGeometry.PresheafedSpace.forget is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u}) [_inst_1 : CategoryTheory.Category.{v, u} C], CategoryTheory.Functor.{v, v, max u (succ v), succ v} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) TopCat.{v} TopCat.largeCategory.{v}
but is expected to have type
  forall (C : Type.{u_1}) [_inst_1 : CategoryTheory.Category.{u_2, u_1} C], CategoryTheory.Functor.{max u_2 u_3, u_3, max (max (succ u_3) u_2) u_1, succ u_3} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1) TopCat.{u_3} instTopCatLargeCategory.{u_3}
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.forget AlgebraicGeometry.PresheafedSpace.forgetₓ'. -/
/-- The forgetful functor from `PresheafedSpace` to `Top`. -/
@[simps]
def forget : PresheafedSpace.{v, v, u} C ⥤ TopCat
    where
  obj X := (X : TopCat.{v})
  map X Y f := f.base
#align algebraic_geometry.PresheafedSpace.forget AlgebraicGeometry.PresheafedSpace.forget

end

section Iso

variable {X Y : PresheafedSpace.{v, v, u} C}

/- warning: algebraic_geometry.PresheafedSpace.iso_of_components -> AlgebraicGeometry.PresheafedSpace.isoOfComponents is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] {X : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} (H : CategoryTheory.Iso.{v, succ v} TopCat.{v} TopCat.largeCategory.{v} (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y)), (CategoryTheory.Iso.{v, max u v} (TopCat.Presheaf.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y)) (TopCat.Presheaf.category.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y)) (TopCat.Presheaf.pushforwardObj.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y) (CategoryTheory.Iso.hom.{v, succ v} TopCat.{v} TopCat.largeCategory.{v} (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y) H) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 Y)) -> (CategoryTheory.Iso.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) X Y)
but is expected to have type
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2, u_1} C] {X : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1} (H : CategoryTheory.Iso.{u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3} (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y)), (CategoryTheory.Iso.{max u_2 u_3, max (max u_1 u_2) u_3} (TopCat.Presheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y)) (TopCat.instCategoryPresheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y)) (TopCat.Presheaf.pushforwardObj.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y) (CategoryTheory.Iso.hom.{u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3} (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y) H) (AlgebraicGeometry.PresheafedSpace.presheaf.{u_1, u_2, u_3} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.presheaf.{u_1, u_2, u_3} C _inst_1 Y)) -> (CategoryTheory.Iso.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1) X Y)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.iso_of_components AlgebraicGeometry.PresheafedSpace.isoOfComponentsₓ'. -/
/-- An isomorphism of PresheafedSpaces is a homeomorphism of the underlying space, and a
natural transformation between the sheaves.
-/
@[simps Hom inv]
def isoOfComponents (H : X.1 ≅ Y.1) (α : H.Hom _* X.2 ≅ Y.2) : X ≅ Y
    where
  Hom :=
    { base := H.Hom
      c := α.inv }
  inv :=
    { base := H.inv
      c := Presheaf.toPushforwardOfIso H α.Hom }
  hom_inv_id' := by ext; · simp; erw [category.id_comp]; simpa; simp
  inv_hom_id' := by
    ext x
    induction x using Opposite.rec'
    simp only [comp_c_app, whisker_right_app, presheaf.to_pushforward_of_iso_app,
      nat_trans.comp_app, eq_to_hom_app, id_c_app, category.assoc]
    erw [← α.hom.naturality]
    have := nat_trans.congr_app α.inv_hom_id (op x)
    cases x
    rw [nat_trans.comp_app] at this
    convert this
    · dsimp; simp
    · simp
    · simp
#align algebraic_geometry.PresheafedSpace.iso_of_components AlgebraicGeometry.PresheafedSpace.isoOfComponents

/- warning: algebraic_geometry.PresheafedSpace.sheaf_iso_of_iso -> AlgebraicGeometry.PresheafedSpace.sheafIsoOfIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] {X : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} (H : CategoryTheory.Iso.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) X Y), CategoryTheory.Iso.{v, max u v} (TopCat.Presheaf.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y)) (TopCat.Presheaf.category.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y)) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 Y) (TopCat.Presheaf.pushforwardObj.{v, v, u} C _inst_1 ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{v, v, u} C _inst_1 X Y (CategoryTheory.Iso.hom.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) X Y H)) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 X))
but is expected to have type
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2, u_1} C] {X : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1} (H : CategoryTheory.Iso.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1) X Y), CategoryTheory.Iso.{max u_2 u_3, max (max u_1 u_2) u_3} (TopCat.Presheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y)) (TopCat.instCategoryPresheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y)) (AlgebraicGeometry.PresheafedSpace.presheaf.{u_1, u_2, u_3} C _inst_1 Y) (TopCat.Presheaf.pushforwardObj.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u_1, u_2, u_3} C _inst_1 X Y (CategoryTheory.Iso.hom.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1) X Y H)) (AlgebraicGeometry.PresheafedSpace.presheaf.{u_1, u_2, u_3} C _inst_1 X))
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.sheaf_iso_of_iso AlgebraicGeometry.PresheafedSpace.sheafIsoOfIsoₓ'. -/
/-- Isomorphic PresheafedSpaces have natural isomorphic presheaves. -/
@[simps]
def sheafIsoOfIso (H : X ≅ Y) : Y.2 ≅ H.Hom.base _* X.2
    where
  Hom := H.Hom.c
  inv := Presheaf.pushforwardToOfIso ((forget _).mapIso H).symm H.inv.c
  hom_inv_id' := by
    ext U
    have := congr_app H.inv_hom_id U
    simp only [comp_c_app, id_c_app, eq_to_hom_map, eq_to_hom_trans] at this
    generalize_proofs h  at this
    simpa using congr_arg (fun f => f ≫ eq_to_hom h.symm) this
  inv_hom_id' := by
    ext U
    simp only [presheaf.pushforward_to_of_iso_app, nat_trans.comp_app, category.assoc,
      nat_trans.id_app, H.hom.c.naturality]
    have := congr_app H.hom_inv_id ((opens.map H.hom.base).op.obj U)
    generalize_proofs h  at this
    simpa using congr_arg (fun f => f ≫ X.presheaf.map (eq_to_hom h.symm)) this
#align algebraic_geometry.PresheafedSpace.sheaf_iso_of_iso AlgebraicGeometry.PresheafedSpace.sheafIsoOfIso

/- warning: algebraic_geometry.PresheafedSpace.base_is_iso_of_iso -> AlgebraicGeometry.PresheafedSpace.base_isIso_of_iso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] {X : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} (f : Quiver.Hom.{succ v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1))) X Y) [_inst_2 : CategoryTheory.IsIso.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) X Y f], CategoryTheory.IsIso.{v, succ v} TopCat.{v} TopCat.largeCategory.{v} ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X) ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{v, v, u} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2, u_1} C] {X : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1} (f : Quiver.Hom.{max (succ u_2) (succ u_3), max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1))) X Y) [_inst_2 : CategoryTheory.IsIso.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1) X Y f], CategoryTheory.IsIso.{u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3} (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u_1, u_2, u_3} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.base_is_iso_of_iso AlgebraicGeometry.PresheafedSpace.base_isIso_of_isoₓ'. -/
instance base_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.base :=
  IsIso.of_iso ((forget _).mapIso (asIso f))
#align algebraic_geometry.PresheafedSpace.base_is_iso_of_iso AlgebraicGeometry.PresheafedSpace.base_isIso_of_iso

/- warning: algebraic_geometry.PresheafedSpace.c_is_iso_of_iso -> AlgebraicGeometry.PresheafedSpace.c_isIso_of_iso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] {X : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} (f : Quiver.Hom.{succ v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1))) X Y) [_inst_2 : CategoryTheory.IsIso.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) X Y f], CategoryTheory.IsIso.{v, max u v} (TopCat.Presheaf.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y)) (TopCat.Presheaf.category.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y)) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 Y) (TopCat.Presheaf.pushforwardObj.{v, v, u} C _inst_1 ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{v, v, u} C _inst_1 X Y f) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.Hom.c.{v, v, u} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2, u_1} C] {X : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1} (f : Quiver.Hom.{max (succ u_2) (succ u_3), max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1))) X Y) [_inst_2 : CategoryTheory.IsIso.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1) X Y f], CategoryTheory.IsIso.{max u_2 u_3, max (max u_1 u_2) u_3} (TopCat.Presheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y)) (TopCat.instCategoryPresheaf.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y)) (AlgebraicGeometry.PresheafedSpace.presheaf.{u_1, u_2, u_3} C _inst_1 Y) (TopCat.Presheaf.pushforwardObj.{u_3, u_2, u_1} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u_1, u_2, u_3} C _inst_1 X Y f) (AlgebraicGeometry.PresheafedSpace.presheaf.{u_1, u_2, u_3} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.Hom.c.{u_1, u_2, u_3} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.c_is_iso_of_iso AlgebraicGeometry.PresheafedSpace.c_isIso_of_isoₓ'. -/
instance c_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.c :=
  IsIso.of_iso (sheafIsoOfIso (asIso f))
#align algebraic_geometry.PresheafedSpace.c_is_iso_of_iso AlgebraicGeometry.PresheafedSpace.c_isIso_of_iso

/- warning: algebraic_geometry.PresheafedSpace.is_iso_of_components -> AlgebraicGeometry.PresheafedSpace.isIso_of_components is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] {X : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1} (f : Quiver.Hom.{succ v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1))) X Y) [_inst_2 : CategoryTheory.IsIso.{v, succ v} TopCat.{v} TopCat.largeCategory.{v} ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X) ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{v, v, u} C _inst_1 X Y f)] [_inst_3 : CategoryTheory.IsIso.{v, max u v} (TopCat.Presheaf.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y)) (TopCat.Presheaf.category.{v, v, u} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y)) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 Y) (TopCat.Presheaf.pushforwardObj.{v, v, u} C _inst_1 ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{v, v, u} C _inst_1 X Y f) (AlgebraicGeometry.PresheafedSpace.presheaf.{v, v, u} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.Hom.c.{v, v, u} C _inst_1 X Y f)], CategoryTheory.IsIso.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) X Y f
but is expected to have type
  forall {C : Type.{u_3}} [_inst_1 : CategoryTheory.Category.{u_1, u_3} C] {X : AlgebraicGeometry.PresheafedSpace.{u_3, u_1, u_2} C _inst_1} {Y : AlgebraicGeometry.PresheafedSpace.{u_3, u_1, u_2} C _inst_1} (f : Quiver.Hom.{max (succ u_1) (succ u_2), max (max u_3 u_1) (succ u_2)} (AlgebraicGeometry.PresheafedSpace.{u_3, u_1, u_2} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u_1 u_2, max (max u_3 u_1) (succ u_2)} (AlgebraicGeometry.PresheafedSpace.{u_3, u_1, u_2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u_1 u_2, max (max u_3 u_1) (succ u_2)} (AlgebraicGeometry.PresheafedSpace.{u_3, u_1, u_2} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_3, u_1, u_2} C _inst_1))) X Y) [_inst_2 : CategoryTheory.IsIso.{u_2, succ u_2} TopCat.{u_2} instTopCatLargeCategory.{u_2} (AlgebraicGeometry.PresheafedSpace.carrier.{u_3, u_1, u_2} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_3, u_1, u_2} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u_3, u_1, u_2} C _inst_1 X Y f)] [_inst_3 : CategoryTheory.IsIso.{max u_1 u_2, max (max u_3 u_1) u_2} (TopCat.Presheaf.{u_2, u_1, u_3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_3, u_1, u_2} C _inst_1 Y)) (TopCat.instCategoryPresheaf.{u_2, u_1, u_3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_3, u_1, u_2} C _inst_1 Y)) (AlgebraicGeometry.PresheafedSpace.presheaf.{u_3, u_1, u_2} C _inst_1 Y) (TopCat.Presheaf.pushforwardObj.{u_2, u_1, u_3} C _inst_1 (AlgebraicGeometry.PresheafedSpace.carrier.{u_3, u_1, u_2} C _inst_1 X) (AlgebraicGeometry.PresheafedSpace.carrier.{u_3, u_1, u_2} C _inst_1 Y) (AlgebraicGeometry.PresheafedSpace.Hom.base.{u_3, u_1, u_2} C _inst_1 X Y f) (AlgebraicGeometry.PresheafedSpace.presheaf.{u_3, u_1, u_2} C _inst_1 X)) (AlgebraicGeometry.PresheafedSpace.Hom.c.{u_3, u_1, u_2} C _inst_1 X Y f)], CategoryTheory.IsIso.{max u_1 u_2, max (max u_3 u_1) (succ u_2)} (AlgebraicGeometry.PresheafedSpace.{u_3, u_1, u_2} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_3, u_1, u_2} C _inst_1) X Y f
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.is_iso_of_components AlgebraicGeometry.PresheafedSpace.isIso_of_componentsₓ'. -/
/-- This could be used in conjunction with `category_theory.nat_iso.is_iso_of_is_iso_app`. -/
theorem isIso_of_components (f : X ⟶ Y) [IsIso f.base] [IsIso f.c] : IsIso f :=
  by
  convert is_iso.of_iso (iso_of_components (as_iso f.base) (as_iso f.c).symm)
  ext; · simpa; · simp
#align algebraic_geometry.PresheafedSpace.is_iso_of_components AlgebraicGeometry.PresheafedSpace.isIso_of_components

end Iso

section Restrict

/- warning: algebraic_geometry.PresheafedSpace.restrict -> AlgebraicGeometry.PresheafedSpace.restrict is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.restrict AlgebraicGeometry.PresheafedSpace.restrictₓ'. -/
/-- The restriction of a presheafed space along an open embedding into the space.
-/
@[simps]
def restrict {U : TopCat} (X : PresheafedSpace.{v, v, u} C) {f : U ⟶ (X : TopCat.{v})}
    (h : OpenEmbedding f) : PresheafedSpace C
    where
  carrier := U
  Presheaf := h.IsOpenMap.Functor.op ⋙ X.Presheaf
#align algebraic_geometry.PresheafedSpace.restrict AlgebraicGeometry.PresheafedSpace.restrict

/- warning: algebraic_geometry.PresheafedSpace.of_restrict -> AlgebraicGeometry.PresheafedSpace.ofRestrict is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.of_restrict AlgebraicGeometry.PresheafedSpace.ofRestrictₓ'. -/
/-- The map from the restriction of a presheafed space.
-/
@[simps]
def ofRestrict {U : TopCat} (X : PresheafedSpace.{v, v, u} C) {f : U ⟶ (X : TopCat.{v})}
    (h : OpenEmbedding f) : X.restrict h ⟶ X
    where
  base := f
  c :=
    { app := fun V => X.Presheaf.map (h.IsOpenMap.Adjunction.counit.app V.unop).op
      naturality' := fun U V f =>
        show _ = _ ≫ X.Presheaf.map _ by rw [← map_comp, ← map_comp]; rfl }
#align algebraic_geometry.PresheafedSpace.of_restrict AlgebraicGeometry.PresheafedSpace.ofRestrict

/- warning: algebraic_geometry.PresheafedSpace.of_restrict_mono -> AlgebraicGeometry.PresheafedSpace.ofRestrict_mono is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] {U : TopCat.{v}} (X : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (f : Quiver.Hom.{succ v, succ v} TopCat.{v} (CategoryTheory.CategoryStruct.toQuiver.{v, succ v} TopCat.{v} (CategoryTheory.Category.toCategoryStruct.{v, succ v} TopCat.{v} TopCat.largeCategory.{v})) U (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (hf : OpenEmbedding.{v, v} (coeSort.{succ (succ v), succ (succ v)} (CategoryTheory.Bundled.{v, v} TopologicalSpace.{v}) Type.{v} (CategoryTheory.Bundled.hasCoeToSort.{v, v} TopologicalSpace.{v}) U) (coeSort.{succ (succ v), succ (succ v)} (CategoryTheory.Bundled.{v, v} TopologicalSpace.{v}) Type.{v} (CategoryTheory.Bundled.hasCoeToSort.{v, v} TopologicalSpace.{v}) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (TopCat.topologicalSpace.{v} U) (TopCat.topologicalSpace.{v} (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (coeFn.{succ v, succ v} (Quiver.Hom.{succ v, succ v} TopCat.{v} (CategoryTheory.CategoryStruct.toQuiver.{v, succ v} TopCat.{v} (CategoryTheory.Category.toCategoryStruct.{v, succ v} TopCat.{v} TopCat.largeCategory.{v})) U (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (fun (_x : ContinuousMap.{v, v} (coeSort.{succ (succ v), succ (succ v)} (CategoryTheory.Bundled.{v, v} TopologicalSpace.{v}) Type.{v} (CategoryTheory.Bundled.hasCoeToSort.{v, v} TopologicalSpace.{v}) U) (coeSort.{succ (succ v), succ (succ v)} (CategoryTheory.Bundled.{v, v} TopologicalSpace.{v}) Type.{v} (CategoryTheory.Bundled.hasCoeToSort.{v, v} TopologicalSpace.{v}) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (CategoryTheory.Bundled.str.{v, v} TopologicalSpace.{v} U) (CategoryTheory.Bundled.str.{v, v} TopologicalSpace.{v} (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X))) => (coeSort.{succ (succ v), succ (succ v)} (CategoryTheory.Bundled.{v, v} TopologicalSpace.{v}) Type.{v} (CategoryTheory.Bundled.hasCoeToSort.{v, v} TopologicalSpace.{v}) U) -> (coeSort.{succ (succ v), succ (succ v)} (CategoryTheory.Bundled.{v, v} TopologicalSpace.{v}) Type.{v} (CategoryTheory.Bundled.hasCoeToSort.{v, v} TopologicalSpace.{v}) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X))) (ContinuousMap.hasCoeToFun.{v, v} (coeSort.{succ (succ v), succ (succ v)} (CategoryTheory.Bundled.{v, v} TopologicalSpace.{v}) Type.{v} (CategoryTheory.Bundled.hasCoeToSort.{v, v} TopologicalSpace.{v}) U) (coeSort.{succ (succ v), succ (succ v)} (CategoryTheory.Bundled.{v, v} TopologicalSpace.{v}) Type.{v} (CategoryTheory.Bundled.hasCoeToSort.{v, v} TopologicalSpace.{v}) (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X)) (CategoryTheory.Bundled.str.{v, v} TopologicalSpace.{v} U) (CategoryTheory.Bundled.str.{v, v} TopologicalSpace.{v} (AlgebraicGeometry.PresheafedSpace.carrier.{v, v, u} C _inst_1 X))) f)), CategoryTheory.Mono.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.restrict.{v, u} C _inst_1 U X f hf) X (AlgebraicGeometry.PresheafedSpace.ofRestrict.{v, u} C _inst_1 U X f hf)
but is expected to have type
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2, u_1} C] {U : TopCat.{u_3}} (X : AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (f : Quiver.Hom.{succ u_3, succ u_3} TopCat.{u_3} (CategoryTheory.CategoryStruct.toQuiver.{u_3, succ u_3} TopCat.{u_3} (CategoryTheory.Category.toCategoryStruct.{u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3})) U (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X)) (hf : OpenEmbedding.{u_3, u_3} (Prefunctor.obj.{succ u_3, succ u_3, succ u_3, succ u_3} TopCat.{u_3} (CategoryTheory.CategoryStruct.toQuiver.{u_3, succ u_3} TopCat.{u_3} (CategoryTheory.Category.toCategoryStruct.{u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3})) Type.{u_3} (CategoryTheory.CategoryStruct.toQuiver.{u_3, succ u_3} Type.{u_3} (CategoryTheory.Category.toCategoryStruct.{u_3, succ u_3} Type.{u_3} CategoryTheory.types.{u_3})) (CategoryTheory.Functor.toPrefunctor.{u_3, u_3, succ u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3} Type.{u_3} CategoryTheory.types.{u_3} (CategoryTheory.forget.{succ u_3, u_3, u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3} TopCat.concreteCategory.{u_3})) U) (Prefunctor.obj.{succ u_3, succ u_3, succ u_3, succ u_3} TopCat.{u_3} (CategoryTheory.CategoryStruct.toQuiver.{u_3, succ u_3} TopCat.{u_3} (CategoryTheory.Category.toCategoryStruct.{u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3})) Type.{u_3} (CategoryTheory.CategoryStruct.toQuiver.{u_3, succ u_3} Type.{u_3} (CategoryTheory.Category.toCategoryStruct.{u_3, succ u_3} Type.{u_3} CategoryTheory.types.{u_3})) (CategoryTheory.Functor.toPrefunctor.{u_3, u_3, succ u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3} Type.{u_3} CategoryTheory.types.{u_3} (CategoryTheory.forget.{succ u_3, u_3, u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3} TopCat.concreteCategory.{u_3})) (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X)) (TopCat.topologicalSpace_forget.{u_3} U) (TopCat.topologicalSpace_forget.{u_3} (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X)) (Prefunctor.map.{succ u_3, succ u_3, succ u_3, succ u_3} TopCat.{u_3} (CategoryTheory.CategoryStruct.toQuiver.{u_3, succ u_3} TopCat.{u_3} (CategoryTheory.Category.toCategoryStruct.{u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3})) Type.{u_3} (CategoryTheory.CategoryStruct.toQuiver.{u_3, succ u_3} Type.{u_3} (CategoryTheory.Category.toCategoryStruct.{u_3, succ u_3} Type.{u_3} CategoryTheory.types.{u_3})) (CategoryTheory.Functor.toPrefunctor.{u_3, u_3, succ u_3, succ u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3} Type.{u_3} CategoryTheory.types.{u_3} (CategoryTheory.forget.{succ u_3, u_3, u_3} TopCat.{u_3} instTopCatLargeCategory.{u_3} TopCat.concreteCategory.{u_3})) U (AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_2, u_3} C _inst_1 X) f)), CategoryTheory.Mono.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.restrict.{u_1, u_2, u_3} C _inst_1 U X f hf) X (AlgebraicGeometry.PresheafedSpace.ofRestrict.{u_1, u_2, u_3} C _inst_1 U X f hf)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.of_restrict_mono AlgebraicGeometry.PresheafedSpace.ofRestrict_monoₓ'. -/
instance ofRestrict_mono {U : TopCat} (X : PresheafedSpace C) (f : U ⟶ X.1) (hf : OpenEmbedding f) :
    Mono (X.of_restrict hf) :=
  by
  haveI : mono f := (TopCat.mono_iff_injective _).mpr hf.inj
  constructor
  intro Z g₁ g₂ eq
  ext V
  · induction V using Opposite.rec'
    have hV : (opens.map (X.of_restrict hf).base).obj (hf.is_open_map.functor.obj V) = V := by ext1;
      exact Set.preimage_image_eq _ hf.inj
    haveI :
      is_iso (hf.is_open_map.adjunction.counit.app (unop (op (hf.is_open_map.functor.obj V)))) :=
      (nat_iso.is_iso_app_of_is_iso
          (whisker_left hf.is_open_map.functor hf.is_open_map.adjunction.counit) V :
        _)
    have := PresheafedSpace.congr_app Eq (op (hf.is_open_map.functor.obj V))
    simp only [PresheafedSpace.comp_c_app, PresheafedSpace.of_restrict_c_app, category.assoc,
      cancel_epi] at this
    have h : _ ≫ _ = _ ≫ _ ≫ _ :=
      congr_arg (fun f => (X.restrict hf).Presheaf.map (eq_to_hom hV).op ≫ f) this
    erw [g₁.c.naturality, g₂.c.naturality_assoc] at h
    simp only [presheaf.pushforward_obj_map, eq_to_hom_op, category.assoc, eq_to_hom_map,
      eq_to_hom_trans] at h
    rw [← is_iso.comp_inv_eq] at h
    simpa using h
  · have := congr_arg PresheafedSpace.hom.base Eq
    simp only [PresheafedSpace.comp_base, PresheafedSpace.of_restrict_base] at this
    rw [cancel_mono] at this
    exact this
#align algebraic_geometry.PresheafedSpace.of_restrict_mono AlgebraicGeometry.PresheafedSpace.ofRestrict_mono

/- warning: algebraic_geometry.PresheafedSpace.restrict_top_presheaf -> AlgebraicGeometry.PresheafedSpace.restrict_top_presheaf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.restrict_top_presheaf AlgebraicGeometry.PresheafedSpace.restrict_top_presheafₓ'. -/
theorem restrict_top_presheaf (X : PresheafedSpace C) :
    (X.restrict (Opens.openEmbedding ⊤)).Presheaf =
      (Opens.inclusionTopIso X.carrier).inv _* X.Presheaf :=
  by dsimp; rw [opens.inclusion_top_functor X.carrier]; rfl
#align algebraic_geometry.PresheafedSpace.restrict_top_presheaf AlgebraicGeometry.PresheafedSpace.restrict_top_presheaf

/- warning: algebraic_geometry.PresheafedSpace.of_restrict_top_c -> AlgebraicGeometry.PresheafedSpace.ofRestrict_top_c is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.of_restrict_top_c AlgebraicGeometry.PresheafedSpace.ofRestrict_top_cₓ'. -/
theorem ofRestrict_top_c (X : PresheafedSpace C) :
    (X.of_restrict (Opens.openEmbedding ⊤)).c =
      eqToHom
        (by
          rw [restrict_top_presheaf, ← presheaf.pushforward.comp_eq]
          erw [iso.inv_hom_id]; rw [presheaf.pushforward.id_eq]) :=
  by
  /- another approach would be to prove the left hand side
       is a natural isoomorphism, but I encountered a universe
       issue when `apply nat_iso.is_iso_of_is_iso_app`. -/
  ext U;
  change X.presheaf.map _ = _; convert eq_to_hom_map _ _ using 1
  congr ; simpa
  · induction U using Opposite.rec'; dsimp; congr ; ext
    exact ⟨fun h => ⟨⟨x, trivial⟩, h, rfl⟩, fun ⟨⟨_, _⟩, h, rfl⟩ => h⟩
#align algebraic_geometry.PresheafedSpace.of_restrict_top_c AlgebraicGeometry.PresheafedSpace.ofRestrict_top_c

/- warning: algebraic_geometry.PresheafedSpace.to_restrict_top -> AlgebraicGeometry.PresheafedSpace.toRestrictTop is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.to_restrict_top AlgebraicGeometry.PresheafedSpace.toRestrictTopₓ'. -/
/- or `rw [opens.inclusion_top_functor, ←comp_obj, ←opens.map_comp_eq],
         erw iso.inv_hom_id, cases U, refl` after `dsimp` -/
/-- The map to the restriction of a presheafed space along the canonical inclusion from the top
subspace.
-/
@[simps]
def toRestrictTop (X : PresheafedSpace C) : X ⟶ X.restrict (Opens.openEmbedding ⊤)
    where
  base := (Opens.inclusionTopIso X.carrier).inv
  c := eqToHom (restrict_top_presheaf X)
#align algebraic_geometry.PresheafedSpace.to_restrict_top AlgebraicGeometry.PresheafedSpace.toRestrictTop

/- warning: algebraic_geometry.PresheafedSpace.restrict_top_iso -> AlgebraicGeometry.PresheafedSpace.restrictTopIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.restrict_top_iso AlgebraicGeometry.PresheafedSpace.restrictTopIsoₓ'. -/
/-- The isomorphism from the restriction to the top subspace.
-/
@[simps]
def restrictTopIso (X : PresheafedSpace C) : X.restrict (Opens.openEmbedding ⊤) ≅ X
    where
  Hom := X.of_restrict _
  inv := X.toRestrictTop
  hom_inv_id' :=
    AlgebraicGeometry.PresheafedSpace.Hom.ext _ _
        (ConcreteCategory.hom_ext _ _ fun ⟨x, _⟩ => rfl) <|
      by erw [comp_c]; rw [X.of_restrict_top_c]; ext; simp
  inv_hom_id' :=
    AlgebraicGeometry.PresheafedSpace.Hom.ext _ _ rfl <| by erw [comp_c]; rw [X.of_restrict_top_c];
      ext; simpa [-eq_to_hom_refl]
#align algebraic_geometry.PresheafedSpace.restrict_top_iso AlgebraicGeometry.PresheafedSpace.restrictTopIso

end Restrict

/- warning: algebraic_geometry.PresheafedSpace.Γ -> AlgebraicGeometry.PresheafedSpace.Γ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C], CategoryTheory.Functor.{v, v, max u (succ v), u} (Opposite.{succ (max u (succ v))} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1)) (CategoryTheory.Category.opposite.{v, max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1)) C _inst_1
but is expected to have type
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2, u_1} C], CategoryTheory.Functor.{max u_2 u_3, u_2, max (max u_1 u_2) (succ u_3), u_1} (Opposite.{max (max (succ (succ u_3)) (succ u_2)) (succ u_1)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1)) (CategoryTheory.Category.opposite.{max u_2 u_3, max (max u_1 u_2) (succ u_3)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_3} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_3} C _inst_1)) C _inst_1
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.Γ AlgebraicGeometry.PresheafedSpace.Γₓ'. -/
/-- The global sections, notated Gamma.
-/
@[simps]
def Γ : (PresheafedSpace.{v, v, u} C)ᵒᵖ ⥤ C
    where
  obj X := (unop X).Presheaf.obj (op ⊤)
  map X Y f := f.unop.c.app (op ⊤)
#align algebraic_geometry.PresheafedSpace.Γ AlgebraicGeometry.PresheafedSpace.Γ

/- warning: algebraic_geometry.PresheafedSpace.Γ_obj_op -> AlgebraicGeometry.PresheafedSpace.Γ_obj_op is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.Γ_obj_op AlgebraicGeometry.PresheafedSpace.Γ_obj_opₓ'. -/
theorem Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.Presheaf.obj (op ⊤) :=
  rfl
#align algebraic_geometry.PresheafedSpace.Γ_obj_op AlgebraicGeometry.PresheafedSpace.Γ_obj_op

/- warning: algebraic_geometry.PresheafedSpace.Γ_map_op -> AlgebraicGeometry.PresheafedSpace.Γ_map_op is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.Γ_map_op AlgebraicGeometry.PresheafedSpace.Γ_map_opₓ'. -/
theorem Γ_map_op {X Y : PresheafedSpace.{v, v, u} C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.PresheafedSpace.Γ_map_op AlgebraicGeometry.PresheafedSpace.Γ_map_op

end PresheafedSpace

end AlgebraicGeometry

open AlgebraicGeometry AlgebraicGeometry.PresheafedSpace

variable {C}

namespace CategoryTheory

variable {D : Type u} [Category.{v} D]

attribute [local simp] presheaf.pushforward_obj

namespace Functor

/- warning: category_theory.functor.map_presheaf -> CategoryTheory.Functor.mapPresheaf is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] {D : Type.{u}} [_inst_2 : CategoryTheory.Category.{v, u} D], (CategoryTheory.Functor.{v, v, u, u} C _inst_1 D _inst_2) -> (CategoryTheory.Functor.{v, v, max u (succ v), max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{v, v, u} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} D _inst_2))
but is expected to have type
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2, u_1} C] {D : Type.{u_3}} [_inst_2 : CategoryTheory.Category.{u_4, u_3} D], (CategoryTheory.Functor.{u_2, u_4, u_1, u_3} C _inst_1 D _inst_2) -> (CategoryTheory.Functor.{max u_2 u_5, max u_4 u_5, max (max (succ u_5) u_2) u_1, max (max (succ u_5) u_4) u_3} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{u_3, u_4, u_5} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_3, u_4, u_5} D _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_presheaf CategoryTheory.Functor.mapPresheafₓ'. -/
/-- We can apply a functor `F : C ⥤ D` to the values of the presheaf in any `PresheafedSpace C`,
    giving a functor `PresheafedSpace C ⥤ PresheafedSpace D` -/
def mapPresheaf (F : C ⥤ D) : PresheafedSpace.{v, v, u} C ⥤ PresheafedSpace.{v, v, u} D
    where
  obj X :=
    { carrier := X.carrier
      Presheaf := X.Presheaf ⋙ F }
  map X Y f :=
    { base := f.base
      c := whiskerRight f.c F }
#align category_theory.functor.map_presheaf CategoryTheory.Functor.mapPresheaf

/- warning: category_theory.functor.map_presheaf_obj_X -> CategoryTheory.Functor.mapPresheaf_obj_X is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] {D : Type.{u}} [_inst_2 : CategoryTheory.Category.{v, u} D] (F : CategoryTheory.Functor.{v, v, u, u} C _inst_1 D _inst_2) (X : AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1), Eq.{succ (succ v)} TopCat.{v} ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} D _inst_2) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} D _inst_2) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} D _inst_2) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} D _inst_2) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} D _inst_2)))) (CategoryTheory.Functor.obj.{v, v, max u (succ v), max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{v, v, u} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} D _inst_2) (CategoryTheory.Functor.mapPresheaf.{v, u} C _inst_1 D _inst_2 F) X)) ((fun (a : Sort.{max (succ u) (succ (succ v))}) (b : Type.{succ v}) [self : HasLiftT.{max (succ u) (succ (succ v)), succ (succ v)} a b] => self.0) (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (HasLiftT.mk.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (CoeTCₓ.coe.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (coeBase.{max (succ u) (succ (succ v)), succ (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) TopCat.{v} (AlgebraicGeometry.PresheafedSpace.coeCarrier.{v, v, u} C _inst_1)))) X)
but is expected to have type
  forall {C : Type.{u_3}} [_inst_1 : CategoryTheory.Category.{u_1, u_3} C] {D : Type.{u_4}} [_inst_2 : CategoryTheory.Category.{u_2, u_4} D] (F : CategoryTheory.Functor.{u_1, u_2, u_3, u_4} C _inst_1 D _inst_2) (X : AlgebraicGeometry.PresheafedSpace.{u_3, u_1, u_5} C _inst_1), Eq.{succ (succ u_5)} TopCat.{u_5} (AlgebraicGeometry.PresheafedSpace.carrier.{u_4, u_2, u_5} D _inst_2 (Prefunctor.obj.{max (succ u_1) (succ u_5), max (succ u_2) (succ u_5), max (max u_3 u_1) (succ u_5), max (max u_4 u_2) (succ u_5)} (AlgebraicGeometry.PresheafedSpace.{u_3, u_1, u_5} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u_1 u_5, max (max u_3 u_1) (succ u_5)} (AlgebraicGeometry.PresheafedSpace.{u_3, u_1, u_5} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u_1 u_5, max (max u_3 u_1) (succ u_5)} (AlgebraicGeometry.PresheafedSpace.{u_3, u_1, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_3, u_1, u_5} C _inst_1))) (AlgebraicGeometry.PresheafedSpace.{u_4, u_2, u_5} D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u_2 u_5, max (max u_4 u_2) (succ u_5)} (AlgebraicGeometry.PresheafedSpace.{u_4, u_2, u_5} D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u_2 u_5, max (max u_4 u_2) (succ u_5)} (AlgebraicGeometry.PresheafedSpace.{u_4, u_2, u_5} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_4, u_2, u_5} D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{max u_1 u_5, max u_2 u_5, max (max u_3 u_1) (succ u_5), max (max u_4 u_2) (succ u_5)} (AlgebraicGeometry.PresheafedSpace.{u_3, u_1, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_3, u_1, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{u_4, u_2, u_5} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_4, u_2, u_5} D _inst_2) (CategoryTheory.Functor.mapPresheaf.{u_3, u_1, u_4, u_2, u_5} C _inst_1 D _inst_2 F)) X)) (AlgebraicGeometry.PresheafedSpace.carrier.{u_3, u_1, u_5} C _inst_1 X)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_presheaf_obj_X CategoryTheory.Functor.mapPresheaf_obj_Xₓ'. -/
@[simp]
theorem mapPresheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X : TopCat.{v}) = (X : TopCat.{v}) :=
  rfl
#align category_theory.functor.map_presheaf_obj_X CategoryTheory.Functor.mapPresheaf_obj_X

/- warning: category_theory.functor.map_presheaf_obj_presheaf -> CategoryTheory.Functor.mapPresheaf_obj_presheaf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_presheaf_obj_presheaf CategoryTheory.Functor.mapPresheaf_obj_presheafₓ'. -/
@[simp]
theorem mapPresheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X).Presheaf = X.Presheaf ⋙ F :=
  rfl
#align category_theory.functor.map_presheaf_obj_presheaf CategoryTheory.Functor.mapPresheaf_obj_presheaf

/- warning: category_theory.functor.map_presheaf_map_f -> CategoryTheory.Functor.mapPresheaf_map_f is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_presheaf_map_f CategoryTheory.Functor.mapPresheaf_map_fₓ'. -/
@[simp]
theorem mapPresheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace.{v, v, u} C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).base = f.base :=
  rfl
#align category_theory.functor.map_presheaf_map_f CategoryTheory.Functor.mapPresheaf_map_f

/- warning: category_theory.functor.map_presheaf_map_c -> CategoryTheory.Functor.mapPresheaf_map_c is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_presheaf_map_c CategoryTheory.Functor.mapPresheaf_map_cₓ'. -/
@[simp]
theorem mapPresheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace.{v, v, u} C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).c = whiskerRight f.c F :=
  rfl
#align category_theory.functor.map_presheaf_map_c CategoryTheory.Functor.mapPresheaf_map_c

end Functor

namespace NatTrans

/- warning: category_theory.nat_trans.on_presheaf -> CategoryTheory.NatTrans.onPresheaf is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u}} [_inst_1 : CategoryTheory.Category.{v, u} C] {D : Type.{u}} [_inst_2 : CategoryTheory.Category.{v, u} D] {F : CategoryTheory.Functor.{v, v, u, u} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{v, v, u, u} C _inst_1 D _inst_2}, (Quiver.Hom.{succ (max u v), max v u} (CategoryTheory.Functor.{v, v, u, u} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u v, max v u} (CategoryTheory.Functor.{v, v, u, u} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u v, max v u} (CategoryTheory.Functor.{v, v, u, u} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{v, v, u, u} C _inst_1 D _inst_2))) F G) -> (Quiver.Hom.{succ (max (max u (succ v)) v), max v u (succ v)} (CategoryTheory.Functor.{v, v, max u (succ v), max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{v, v, u} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} D _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max (max u (succ v)) v, max v u (succ v)} (CategoryTheory.Functor.{v, v, max u (succ v), max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{v, v, u} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} D _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max (max u (succ v)) v, max v u (succ v)} (CategoryTheory.Functor.{v, v, max u (succ v), max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{v, v, u} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} D _inst_2)) (CategoryTheory.Functor.category.{v, v, max u (succ v), max u (succ v)} (AlgebraicGeometry.PresheafedSpace.{v, v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{v, v, u} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{v, u} D _inst_2)))) (CategoryTheory.Functor.mapPresheaf.{v, u} C _inst_1 D _inst_2 G) (CategoryTheory.Functor.mapPresheaf.{v, u} C _inst_1 D _inst_2 F))
but is expected to have type
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2, u_1} C] {D : Type.{u_3}} [_inst_2 : CategoryTheory.Category.{u_4, u_3} D] {F : CategoryTheory.Functor.{u_2, u_4, u_1, u_3} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u_2, u_4, u_1, u_3} C _inst_1 D _inst_2}, (Quiver.Hom.{max (succ u_1) (succ u_4), max (max (max u_1 u_2) u_3) u_4} (CategoryTheory.Functor.{u_2, u_4, u_1, u_3} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u_1 u_4, max (max (max u_1 u_2) u_3) u_4} (CategoryTheory.Functor.{u_2, u_4, u_1, u_3} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u_1 u_4, max (max (max u_1 u_2) u_3) u_4} (CategoryTheory.Functor.{u_2, u_4, u_1, u_3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u_2, u_4, u_1, u_3} C _inst_1 D _inst_2))) F G) -> (Quiver.Hom.{max (max (max (succ u_1) (succ u_2)) (succ u_4)) (succ (succ u_5)), max (max (max (max u_1 u_2) u_3) u_4) (succ u_5)} (CategoryTheory.Functor.{max u_2 u_5, max u_4 u_5, max (max (succ u_5) u_2) u_1, max (max (succ u_5) u_4) u_3} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{u_3, u_4, u_5} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_3, u_4, u_5} D _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max (max (max u_1 u_2) u_4) (succ u_5), max (max (max (max u_1 u_2) u_3) u_4) (succ u_5)} (CategoryTheory.Functor.{max u_2 u_5, max u_4 u_5, max (max (succ u_5) u_2) u_1, max (max (succ u_5) u_4) u_3} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{u_3, u_4, u_5} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_3, u_4, u_5} D _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max (max (max u_1 u_2) u_4) (succ u_5), max (max (max (max u_1 u_2) u_3) u_4) (succ u_5)} (CategoryTheory.Functor.{max u_2 u_5, max u_4 u_5, max (max (succ u_5) u_2) u_1, max (max (succ u_5) u_4) u_3} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{u_3, u_4, u_5} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_3, u_4, u_5} D _inst_2)) (CategoryTheory.Functor.category.{max u_2 u_5, max u_4 u_5, max (max u_1 u_2) (succ u_5), max (max u_3 u_4) (succ u_5)} (AlgebraicGeometry.PresheafedSpace.{u_1, u_2, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_1, u_2, u_5} C _inst_1) (AlgebraicGeometry.PresheafedSpace.{u_3, u_4, u_5} D _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u_3, u_4, u_5} D _inst_2)))) (CategoryTheory.Functor.mapPresheaf.{u_1, u_2, u_3, u_4, u_5} C _inst_1 D _inst_2 G) (CategoryTheory.Functor.mapPresheaf.{u_1, u_2, u_3, u_4, u_5} C _inst_1 D _inst_2 F))
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.on_presheaf CategoryTheory.NatTrans.onPresheafₓ'. -/
/-- A natural transformation induces a natural transformation between the `map_presheaf` functors.
-/
def onPresheaf {F G : C ⥤ D} (α : F ⟶ G) : G.mapPresheaf ⟶ F.mapPresheaf
    where app X :=
    { base := 𝟙 _
      c := whiskerLeft X.Presheaf α ≫ eqToHom (Presheaf.Pushforward.id_eq _).symm }
#align category_theory.nat_trans.on_presheaf CategoryTheory.NatTrans.onPresheaf

-- TODO Assemble the last two constructions into a functor
--   `(C ⥤ D) ⥤ (PresheafedSpace C ⥤ PresheafedSpace D)`
end NatTrans

end CategoryTheory

