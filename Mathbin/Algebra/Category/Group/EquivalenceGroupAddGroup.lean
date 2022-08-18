/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathbin.Algebra.Category.Group.Basic

/-!
# Equivalence between `Group` and `AddGroup`

This file contains two equivalences:
* `Group_AddGroup_equivalence` : the equivalence between `Group` and `AddGroup` by sending
  `X : Group` to `additive X` and `Y : AddGroup` to `multiplicative Y`.
* `CommGroup_AddCommGroup_equivalence` : the equivalence between `CommGroup` and `AddCommGroup` by
  sending `X : CommGroup` to `additive X` and `Y : AddCommGroup` to `multiplicative Y`.
-/


open CategoryTheory

namespace Groupₓₓ

/-- The functor `Group ⥤ AddGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps]
def toAddGroup : Groupₓₓ ⥤ AddGroupₓₓ where
  obj := fun X => AddGroupₓₓ.of (Additive X)
  map := fun X Y => MonoidHom.toAdditive

end Groupₓₓ

namespace CommGroupₓₓ

/-- The functor `CommGroup ⥤ AddCommGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps]
def toAddCommGroup : CommGroupₓₓ ⥤ AddCommGroupₓₓ where
  obj := fun X => AddCommGroupₓₓ.of (Additive X)
  map := fun X Y => MonoidHom.toAdditive

end CommGroupₓₓ

namespace AddGroupₓₓ

/-- The functor `AddGroup ⥤ Group` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps]
def toGroup : AddGroupₓₓ ⥤ Groupₓₓ where
  obj := fun X => Groupₓₓ.of (Multiplicative X)
  map := fun X Y => AddMonoidHom.toMultiplicative

end AddGroupₓₓ

namespace AddCommGroupₓₓ

/-- The functor `AddCommGroup ⥤ CommGroup` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps]
def toCommGroup : AddCommGroupₓₓ ⥤ CommGroupₓₓ where
  obj := fun X => CommGroupₓₓ.of (Multiplicative X)
  map := fun X Y => AddMonoidHom.toMultiplicative

end AddCommGroupₓₓ

/-- The equivalence of categories between `Group` and `AddGroup`
-/
@[simps]
def groupAddGroupEquivalence : Groupₓₓ ≌ AddGroupₓₓ :=
  Equivalence.mk Groupₓₓ.toAddGroup AddGroupₓₓ.toGroup
    (NatIso.ofComponents (fun X => MulEquiv.toGroupIso (MulEquiv.multiplicativeAdditive X)) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => AddEquiv.toAddGroupIso (AddEquiv.additiveMultiplicative X)) fun X Y f => rfl)

/-- The equivalence of categories between `CommGroup` and `AddCommGroup`.
-/
@[simps]
def commGroupAddCommGroupEquivalence : CommGroupₓₓ ≌ AddCommGroupₓₓ :=
  Equivalence.mk CommGroupₓₓ.toAddCommGroup AddCommGroupₓₓ.toCommGroup
    (NatIso.ofComponents (fun X => MulEquiv.toCommGroupIso (MulEquiv.multiplicativeAdditive X)) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => AddEquiv.toAddCommGroupIso (AddEquiv.additiveMultiplicative X)) fun X Y f => rfl)

