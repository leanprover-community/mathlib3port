/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module algebra.category.Group.equivalence_Group_AddGroup
! leanprover-community/mathlib commit 781cb2eed038c4caf53bdbd8d20a95e5822d77df
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.Basic
import Mathbin.Algebra.Hom.Equiv.TypeTags

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

namespace GroupCat

#print GroupCat.toAddGroupCat /-
/-- The functor `Group ⥤ AddGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps]
def toAddGroupCat : GroupCat ⥤ AddGroupCat
    where
  obj X := AddGroupCat.of (Additive X)
  map X Y := MonoidHom.toAdditive
#align Group.to_AddGroup GroupCat.toAddGroupCat
-/

end GroupCat

namespace CommGroupCat

#print CommGroupCat.toAddCommGroupCat /-
/-- The functor `CommGroup ⥤ AddCommGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps]
def toAddCommGroupCat : CommGroupCat ⥤ AddCommGroupCat
    where
  obj X := AddCommGroupCat.of (Additive X)
  map X Y := MonoidHom.toAdditive
#align CommGroup.to_AddCommGroup CommGroupCat.toAddCommGroupCat
-/

end CommGroupCat

namespace AddGroupCat

#print AddGroupCat.toGroupCat /-
/-- The functor `AddGroup ⥤ Group` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps]
def toGroupCat : AddGroupCat ⥤ GroupCat
    where
  obj X := GroupCat.of (Multiplicative X)
  map X Y := AddMonoidHom.toMultiplicative
#align AddGroup.to_Group AddGroupCat.toGroupCat
-/

end AddGroupCat

namespace AddCommGroupCat

#print AddCommGroupCat.toCommGroupCat /-
/-- The functor `AddCommGroup ⥤ CommGroup` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps]
def toCommGroupCat : AddCommGroupCat ⥤ CommGroupCat
    where
  obj X := CommGroupCat.of (Multiplicative X)
  map X Y := AddMonoidHom.toMultiplicative
#align AddCommGroup.to_CommGroup AddCommGroupCat.toCommGroupCat
-/

end AddCommGroupCat

#print groupAddGroupEquivalence /-
/-- The equivalence of categories between `Group` and `AddGroup`
-/
@[simps]
def groupAddGroupEquivalence : GroupCat ≌ AddGroupCat :=
  Equivalence.mk GroupCat.toAddGroupCat AddGroupCat.toGroupCat
    (NatIso.ofComponents (fun X => MulEquiv.toGroupCatIso (MulEquiv.multiplicativeAdditive X))
      fun X Y f => rfl)
    (NatIso.ofComponents (fun X => AddEquiv.toAddGroupCatIso (AddEquiv.additiveMultiplicative X))
      fun X Y f => rfl)
#align Group_AddGroup_equivalence groupAddGroupEquivalence
-/

#print commGroupAddCommGroupEquivalence /-
/-- The equivalence of categories between `CommGroup` and `AddCommGroup`.
-/
@[simps]
def commGroupAddCommGroupEquivalence : CommGroupCat ≌ AddCommGroupCat :=
  Equivalence.mk CommGroupCat.toAddCommGroupCat AddCommGroupCat.toCommGroupCat
    (NatIso.ofComponents (fun X => MulEquiv.toCommGroupCatIso (MulEquiv.multiplicativeAdditive X))
      fun X Y f => rfl)
    (NatIso.ofComponents
      (fun X => AddEquiv.toAddCommGroupCatIso (AddEquiv.additiveMultiplicative X)) fun X Y f => rfl)
#align CommGroup_AddCommGroup_equivalence commGroupAddCommGroupEquivalence
-/

