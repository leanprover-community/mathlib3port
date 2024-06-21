/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Algebra.Category.Grp.Basic
import Algebra.Group.Equiv.TypeTags

#align_import algebra.category.Group.equivalence_Group_AddGroup from "leanprover-community/mathlib"@"781cb2eed038c4caf53bdbd8d20a95e5822d77df"

/-!
# Equivalence between `Group` and `AddGroup`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains two equivalences:
* `Group_AddGroup_equivalence` : the equivalence between `Group` and `AddGroup` by sending
  `X : Group` to `additive X` and `Y : AddGroup` to `multiplicative Y`.
* `CommGroup_AddCommGroup_equivalence` : the equivalence between `CommGroup` and `AddCommGroup` by
  sending `X : CommGroup` to `additive X` and `Y : AddCommGroup` to `multiplicative Y`.
-/


open CategoryTheory

namespace Grp

#print Grp.toAddGrp /-
/-- The functor `Group ⥤ AddGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps]
def toAddGrp : Grp ⥤ AddGrp where
  obj X := AddGrp.of (Additive X)
  map X Y := MonoidHom.toAdditive
#align Group.to_AddGroup Grp.toAddGrp
-/

end Grp

namespace CommGrp

#print CommGrp.toAddCommGrp /-
/-- The functor `CommGroup ⥤ AddCommGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps]
def toAddCommGrp : CommGrp ⥤ AddCommGrp
    where
  obj X := AddCommGrp.of (Additive X)
  map X Y := MonoidHom.toAdditive
#align CommGroup.to_AddCommGroup CommGrp.toAddCommGrp
-/

end CommGrp

namespace AddGrp

#print AddGrp.toGrp /-
/-- The functor `AddGroup ⥤ Group` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps]
def toGrp : AddGrp ⥤ Grp where
  obj X := Grp.of (Multiplicative X)
  map X Y := AddMonoidHom.toMultiplicative
#align AddGroup.to_Group AddGrp.toGrp
-/

end AddGrp

namespace AddCommGrp

#print AddCommGrp.toCommGrp /-
/-- The functor `AddCommGroup ⥤ CommGroup` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps]
def toCommGrp : AddCommGrp ⥤ CommGrp
    where
  obj X := CommGrp.of (Multiplicative X)
  map X Y := AddMonoidHom.toMultiplicative
#align AddCommGroup.to_CommGroup AddCommGrp.toCommGrp
-/

end AddCommGrp

#print groupAddGroupEquivalence /-
/-- The equivalence of categories between `Group` and `AddGroup`
-/
@[simps]
def groupAddGroupEquivalence : Grp ≌ AddGrp :=
  Equivalence.mk Grp.toAddGrp AddGrp.toGrp
    (NatIso.ofComponents (fun X => MulEquiv.toGrpIso (MulEquiv.multiplicativeAdditive X))
      fun X Y f => rfl)
    (NatIso.ofComponents (fun X => AddEquiv.toAddGrpIso (AddEquiv.additiveMultiplicative X))
      fun X Y f => rfl)
#align Group_AddGroup_equivalence groupAddGroupEquivalence
-/

#print commGroupAddCommGroupEquivalence /-
/-- The equivalence of categories between `CommGroup` and `AddCommGroup`.
-/
@[simps]
def commGroupAddCommGroupEquivalence : CommGrp ≌ AddCommGrp :=
  Equivalence.mk CommGrp.toAddCommGrp AddCommGrp.toCommGrp
    (NatIso.ofComponents (fun X => MulEquiv.toCommGrpIso (MulEquiv.multiplicativeAdditive X))
      fun X Y f => rfl)
    (NatIso.ofComponents (fun X => AddEquiv.toAddCommGrpIso (AddEquiv.additiveMultiplicative X))
      fun X Y f => rfl)
#align CommGroup_AddCommGroup_equivalence commGroupAddCommGroupEquivalence
-/

