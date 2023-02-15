/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.group_action.units
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.Defs

/-! # Group actions on and by `Mˣ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the action of a unit on a type `α`, `has_smul Mˣ α`, in the presence of
`has_smul M α`, with the obvious definition stated in `units.smul_def`. This definition preserves
`mul_action` and `distrib_mul_action` structures too.

Additionally, a `mul_action G M` for some group `G` satisfying some additional properties admits a
`mul_action G Mˣ` structure, again with the obvious definition stated in `units.coe_smul`.
These instances use a primed name.

The results are repeated for `add_units` and `has_vadd` where relevant.
-/


variable {G H M N : Type _} {α : Type _}

namespace Units

/-! ### Action of the units of `M` on a type `α` -/


@[to_additive]
instance [Monoid M] [SMul M α] : SMul Mˣ α where smul m a := (m : M) • a

/- warning: units.smul_def -> Units.smul_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : SMul.{u1, u2} M α] (m : Units.{u1} M _inst_1) (a : α), Eq.{succ u2} α (SMul.smul.{u1, u2} (Units.{u1} M _inst_1) α (Units.hasSmul.{u1, u2} M α _inst_1 _inst_2) m a) (SMul.smul.{u1, u2} M α _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) m) a)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : SMul.{u2, u1} M α] (m : Units.{u2} M _inst_1) (a : α), Eq.{succ u1} α (HSMul.hSMul.{u2, u1, u1} (Units.{u2} M _inst_1) α α (instHSMul.{u2, u1} (Units.{u2} M _inst_1) α (Units.instSMulUnits.{u2, u1} M α _inst_1 _inst_2)) m a) (HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α _inst_2) (Units.val.{u2} M _inst_1 m) a)
Case conversion may be inaccurate. Consider using '#align units.smul_def Units.smul_defₓ'. -/
@[to_additive]
theorem smul_def [Monoid M] [SMul M α] (m : Mˣ) (a : α) : m • a = (m : M) • a :=
  rfl
#align units.smul_def Units.smul_def
#align add_units.vadd_def AddUnits.vadd_def

/- warning: units.smul_is_unit -> Units.smul_isUnit is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : SMul.{u1, u2} M α] {m : M} (hm : IsUnit.{u1} M _inst_1 m) (a : α), Eq.{succ u2} α (SMul.smul.{u1, u2} (Units.{u1} M _inst_1) α (Units.hasSmul.{u1, u2} M α _inst_1 _inst_2) (IsUnit.unit.{u1} M _inst_1 m hm) a) (SMul.smul.{u1, u2} M α _inst_2 m a)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : SMul.{u2, u1} M α] {m : M} (hm : IsUnit.{u2} M _inst_1 m) (a : α), Eq.{succ u1} α (HSMul.hSMul.{u2, u1, u1} (Units.{u2} M _inst_1) α α (instHSMul.{u2, u1} (Units.{u2} M _inst_1) α (Units.instSMulUnits.{u2, u1} M α _inst_1 _inst_2)) (IsUnit.unit.{u2} M _inst_1 m hm) a) (HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α _inst_2) m a)
Case conversion may be inaccurate. Consider using '#align units.smul_is_unit Units.smul_isUnitₓ'. -/
@[simp]
theorem smul_isUnit [Monoid M] [SMul M α] {m : M} (hm : IsUnit m) (a : α) : hm.Unit • a = m • a :=
  rfl
#align units.smul_is_unit Units.smul_isUnit

/- warning: is_unit.inv_smul -> IsUnit.inv_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} (h : IsUnit.{u1} α _inst_1 a), Eq.{succ u1} α (SMul.smul.{u1, u1} (Units.{u1} α _inst_1) α (Units.hasSmul.{u1, u1} α α _inst_1 (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Inv.inv.{u1} (Units.{u1} α _inst_1) (Units.hasInv.{u1} α _inst_1) (IsUnit.unit.{u1} α _inst_1 a h)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} (h : IsUnit.{u1} α _inst_1 a), Eq.{succ u1} α (HSMul.hSMul.{u1, u1, u1} (Units.{u1} α _inst_1) α α (instHSMul.{u1, u1} (Units.{u1} α _inst_1) α (Units.instSMulUnits.{u1, u1} α α _inst_1 (MulAction.toSMul.{u1, u1} α α _inst_1 (Monoid.toMulAction.{u1} α _inst_1)))) (Inv.inv.{u1} (Units.{u1} α _inst_1) (Units.instInvUnits.{u1} α _inst_1) (IsUnit.unit.{u1} α _inst_1 a h)) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_unit.inv_smul IsUnit.inv_smulₓ'. -/
theorem IsUnit.inv_smul [Monoid α] {a : α} (h : IsUnit a) : h.Unit⁻¹ • a = 1 :=
  h.val_inv_mul
#align is_unit.inv_smul IsUnit.inv_smul

@[to_additive]
instance [Monoid M] [SMul M α] [FaithfulSMul M α] : FaithfulSMul Mˣ α
    where eq_of_smul_eq_smul u₁ u₂ h := Units.ext <| eq_of_smul_eq_smul h

@[to_additive]
instance [Monoid M] [MulAction M α] : MulAction Mˣ α
    where
  one_smul := (one_smul M : _)
  mul_smul m n := mul_smul (m : M) n

instance [Monoid M] [Zero α] [SMulZeroClass M α] : SMulZeroClass Mˣ α
    where
  smul := (· • ·)
  smul_zero m := smul_zero m

instance [Monoid M] [AddZeroClass α] [DistribSMul M α] : DistribSMul Mˣ α
    where smul_add m := smul_add (m : M)

instance [Monoid M] [AddMonoid α] [DistribMulAction M α] : DistribMulAction Mˣ α :=
  { Units.distribSmul with }

instance [Monoid M] [Monoid α] [MulDistribMulAction M α] : MulDistribMulAction Mˣ α
    where
  smul_mul m := smul_mul' (m : M)
  smul_one m := smul_one m

#print Units.smulCommClass_left /-
instance smulCommClass_left [Monoid M] [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass Mˣ N α where smul_comm m n := (smul_comm (m : M) n : _)
#align units.smul_comm_class_left Units.smulCommClass_left
-/

#print Units.smulCommClass_right /-
instance smulCommClass_right [Monoid N] [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M Nˣ α where smul_comm m n := (smul_comm m (n : N) : _)
#align units.smul_comm_class_right Units.smulCommClass_right
-/

instance [Monoid M] [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower Mˣ N α
    where smul_assoc m n := (smul_assoc (m : M) n : _)

/-! ### Action of a group `G` on units of `M` -/


/- warning: units.mul_action' -> Units.mulAction' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {M : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Monoid.{u2} M] [_inst_3 : MulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_4 : SMulCommClass.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)))] [_inst_5 : IsScalarTower.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))) (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3)], MulAction.{u1, u2} G (Units.{u2} M _inst_2) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))
but is expected to have type
  forall {G : Type.{u1}} {M : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Monoid.{u2} M] [_inst_3 : MulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_4 : SMulCommClass.{u1, u2, u2} G M M (MulAction.toSMul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (MulAction.toSMul.{u2, u2} M M _inst_2 (Monoid.toMulAction.{u2} M _inst_2))] [_inst_5 : IsScalarTower.{u1, u2, u2} G M M (MulAction.toSMul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (MulAction.toSMul.{u2, u2} M M _inst_2 (Monoid.toMulAction.{u2} M _inst_2)) (MulAction.toSMul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3)], MulAction.{u1, u2} G (Units.{u2} M _inst_2) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align units.mul_action' Units.mulAction'ₓ'. -/
/-- If an action `G` associates and commutes with multiplication on `M`, then it lifts to an
action on `Mˣ`. Notably, this provides `mul_action Mˣ Nˣ` under suitable
conditions.
-/
instance mulAction' [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M]
    [IsScalarTower G M M] : MulAction G Mˣ
    where
  smul g m :=
    ⟨g • (m : M), g⁻¹ • ↑m⁻¹, by rw [smul_mul_smul, Units.mul_inv, mul_right_inv, one_smul], by
      rw [smul_mul_smul, Units.inv_mul, mul_left_inv, one_smul]⟩
  one_smul m := Units.ext <| one_smul _ _
  mul_smul g₁ g₂ m := Units.ext <| mul_smul _ _ _
#align units.mul_action' Units.mulAction'

/- warning: units.coe_smul -> Units.val_smul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {M : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Monoid.{u2} M] [_inst_3 : MulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_4 : SMulCommClass.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)))] [_inst_5 : IsScalarTower.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))) (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3)] (g : G) (m : Units.{u2} M _inst_2), Eq.{succ u2} M ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} M _inst_2) M (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} M _inst_2) M (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} M _inst_2) M (coeBase.{succ u2, succ u2} (Units.{u2} M _inst_2) M (Units.hasCoe.{u2} M _inst_2)))) (SMul.smul.{u1, u2} G (Units.{u2} M _inst_2) (MulAction.toHasSmul.{u1, u2} G (Units.{u2} M _inst_2) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Units.mulAction'.{u1, u2} G M _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) g m)) (SMul.smul.{u1, u2} G M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) g ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} M _inst_2) M (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} M _inst_2) M (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} M _inst_2) M (coeBase.{succ u2, succ u2} (Units.{u2} M _inst_2) M (Units.hasCoe.{u2} M _inst_2)))) m))
but is expected to have type
  forall {G : Type.{u2}} {M : Type.{u1}} [_inst_1 : Group.{u2} G] [_inst_2 : Monoid.{u1} M] [_inst_3 : MulAction.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))] [_inst_4 : SMulCommClass.{u2, u1, u1} G M M (MulAction.toSMul.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_3) (MulAction.toSMul.{u1, u1} M M _inst_2 (Monoid.toMulAction.{u1} M _inst_2))] [_inst_5 : IsScalarTower.{u2, u1, u1} G M M (MulAction.toSMul.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_3) (MulAction.toSMul.{u1, u1} M M _inst_2 (Monoid.toMulAction.{u1} M _inst_2)) (MulAction.toSMul.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_3)] (g : G) (m : Units.{u1} M _inst_2), Eq.{succ u1} M (Units.val.{u1} M _inst_2 (HSMul.hSMul.{u2, u1, u1} G (Units.{u1} M _inst_2) (Units.{u1} M _inst_2) (instHSMul.{u2, u1} G (Units.{u1} M _inst_2) (MulAction.toSMul.{u2, u1} G (Units.{u1} M _inst_2) (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) (Units.mulAction'.{u2, u1} G M _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))) g m)) (HSMul.hSMul.{u2, u1, u1} G M M (instHSMul.{u2, u1} G M (MulAction.toSMul.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_3)) g (Units.val.{u1} M _inst_2 m))
Case conversion may be inaccurate. Consider using '#align units.coe_smul Units.val_smulₓ'. -/
@[simp]
theorem val_smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : ↑(g • m) = g • (m : M) :=
  rfl
#align units.coe_smul Units.val_smul

/- warning: units.smul_inv -> Units.smul_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {M : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Monoid.{u2} M] [_inst_3 : MulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_4 : SMulCommClass.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)))] [_inst_5 : IsScalarTower.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))) (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3)] (g : G) (m : Units.{u2} M _inst_2), Eq.{succ u2} (Units.{u2} M _inst_2) (Inv.inv.{u2} (Units.{u2} M _inst_2) (Units.hasInv.{u2} M _inst_2) (SMul.smul.{u1, u2} G (Units.{u2} M _inst_2) (MulAction.toHasSmul.{u1, u2} G (Units.{u2} M _inst_2) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Units.mulAction'.{u1, u2} G M _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) g m)) (SMul.smul.{u1, u2} G (Units.{u2} M _inst_2) (MulAction.toHasSmul.{u1, u2} G (Units.{u2} M _inst_2) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Units.mulAction'.{u1, u2} G M _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) g) (Inv.inv.{u2} (Units.{u2} M _inst_2) (Units.hasInv.{u2} M _inst_2) m))
but is expected to have type
  forall {G : Type.{u2}} {M : Type.{u1}} [_inst_1 : Group.{u2} G] [_inst_2 : Monoid.{u1} M] [_inst_3 : MulAction.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))] [_inst_4 : SMulCommClass.{u2, u1, u1} G M M (MulAction.toSMul.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_3) (MulAction.toSMul.{u1, u1} M M _inst_2 (Monoid.toMulAction.{u1} M _inst_2))] [_inst_5 : IsScalarTower.{u2, u1, u1} G M M (MulAction.toSMul.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_3) (MulAction.toSMul.{u1, u1} M M _inst_2 (Monoid.toMulAction.{u1} M _inst_2)) (MulAction.toSMul.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_3)] (g : G) (m : Units.{u1} M _inst_2), Eq.{succ u1} (Units.{u1} M _inst_2) (Inv.inv.{u1} (Units.{u1} M _inst_2) (Units.instInvUnits.{u1} M _inst_2) (HSMul.hSMul.{u2, u1, u1} G (Units.{u1} M _inst_2) (Units.{u1} M _inst_2) (instHSMul.{u2, u1} G (Units.{u1} M _inst_2) (MulAction.toSMul.{u2, u1} G (Units.{u1} M _inst_2) (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) (Units.mulAction'.{u2, u1} G M _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))) g m)) (HSMul.hSMul.{u2, u1, u1} G (Units.{u1} M _inst_2) (Units.{u1} M _inst_2) (instHSMul.{u2, u1} G (Units.{u1} M _inst_2) (MulAction.toSMul.{u2, u1} G (Units.{u1} M _inst_2) (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) (Units.mulAction'.{u2, u1} G M _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))) (Inv.inv.{u2} G (InvOneClass.toInv.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (Group.toDivisionMonoid.{u2} G _inst_1)))) g) (Inv.inv.{u1} (Units.{u1} M _inst_2) (Units.instInvUnits.{u1} M _inst_2) m))
Case conversion may be inaccurate. Consider using '#align units.smul_inv Units.smul_invₓ'. -/
/-- Note that this lemma exists more generally as the global `smul_inv` -/
@[simp]
theorem smul_inv [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : (g • m)⁻¹ = g⁻¹ • m⁻¹ :=
  ext rfl
#align units.smul_inv Units.smul_inv

/- warning: units.smul_comm_class' -> Units.smulCommClass' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {M : Type.{u3}} [_inst_1 : Group.{u1} G] [_inst_2 : Group.{u2} H] [_inst_3 : Monoid.{u3} M] [_inst_4 : MulAction.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_5 : SMulCommClass.{u1, u3, u3} G M M (MulAction.toHasSmul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_4) (Mul.toSMul.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3)))] [_inst_6 : MulAction.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))] [_inst_7 : SMulCommClass.{u2, u3, u3} H M M (MulAction.toHasSmul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)) _inst_6) (Mul.toSMul.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3)))] [_inst_8 : IsScalarTower.{u1, u3, u3} G M M (MulAction.toHasSmul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_4) (Mul.toSMul.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3))) (MulAction.toHasSmul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_4)] [_inst_9 : IsScalarTower.{u2, u3, u3} H M M (MulAction.toHasSmul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)) _inst_6) (Mul.toSMul.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3))) (MulAction.toHasSmul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)) _inst_6)] [_inst_10 : SMulCommClass.{u1, u2, u3} G H M (MulAction.toHasSmul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_4) (MulAction.toHasSmul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)) _inst_6)], SMulCommClass.{u1, u2, u3} G H (Units.{u3} M _inst_3) (MulAction.toHasSmul.{u1, u3} G (Units.{u3} M _inst_3) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Units.mulAction'.{u1, u3} G M _inst_1 _inst_3 _inst_4 _inst_5 _inst_8)) (MulAction.toHasSmul.{u2, u3} H (Units.{u3} M _inst_3) (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)) (Units.mulAction'.{u2, u3} H M _inst_2 _inst_3 _inst_6 _inst_7 _inst_9))
but is expected to have type
  forall {G : Type.{u1}} {H : Type.{u2}} {M : Type.{u3}} [_inst_1 : Group.{u1} G] [_inst_2 : Group.{u2} H] [_inst_3 : Monoid.{u3} M] [_inst_4 : MulAction.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_5 : SMulCommClass.{u1, u3, u3} G M M (MulAction.toSMul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_4) (MulAction.toSMul.{u3, u3} M M _inst_3 (Monoid.toMulAction.{u3} M _inst_3))] [_inst_6 : MulAction.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))] [_inst_7 : SMulCommClass.{u2, u3, u3} H M M (MulAction.toSMul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)) _inst_6) (MulAction.toSMul.{u3, u3} M M _inst_3 (Monoid.toMulAction.{u3} M _inst_3))] [_inst_8 : IsScalarTower.{u1, u3, u3} G M M (MulAction.toSMul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_4) (MulAction.toSMul.{u3, u3} M M _inst_3 (Monoid.toMulAction.{u3} M _inst_3)) (MulAction.toSMul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_4)] [_inst_9 : IsScalarTower.{u2, u3, u3} H M M (MulAction.toSMul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)) _inst_6) (MulAction.toSMul.{u3, u3} M M _inst_3 (Monoid.toMulAction.{u3} M _inst_3)) (MulAction.toSMul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)) _inst_6)] [_inst_10 : SMulCommClass.{u1, u2, u3} G H M (MulAction.toSMul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_4) (MulAction.toSMul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)) _inst_6)], SMulCommClass.{u1, u2, u3} G H (Units.{u3} M _inst_3) (MulAction.toSMul.{u1, u3} G (Units.{u3} M _inst_3) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Units.mulAction'.{u1, u3} G M _inst_1 _inst_3 _inst_4 _inst_5 _inst_8)) (MulAction.toSMul.{u2, u3} H (Units.{u3} M _inst_3) (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)) (Units.mulAction'.{u2, u3} H M _inst_2 _inst_3 _inst_6 _inst_7 _inst_9))
Case conversion may be inaccurate. Consider using '#align units.smul_comm_class' Units.smulCommClass'ₓ'. -/
/-- Transfer `smul_comm_class G H M` to `smul_comm_class G H Mˣ` -/
instance smulCommClass' [Group G] [Group H] [Monoid M] [MulAction G M] [SMulCommClass G M M]
    [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M] [IsScalarTower H M M]
    [SMulCommClass G H M] : SMulCommClass G H Mˣ
    where smul_comm g h m := Units.ext <| smul_comm g h (m : M)
#align units.smul_comm_class' Units.smulCommClass'

/- warning: units.is_scalar_tower' -> Units.isScalarTower' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {M : Type.{u3}} [_inst_1 : SMul.{u1, u2} G H] [_inst_2 : Group.{u1} G] [_inst_3 : Group.{u2} H] [_inst_4 : Monoid.{u3} M] [_inst_5 : MulAction.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_6 : SMulCommClass.{u1, u3, u3} G M M (MulAction.toHasSmul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_5) (Mul.toSMul.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_4)))] [_inst_7 : MulAction.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))] [_inst_8 : SMulCommClass.{u2, u3, u3} H M M (MulAction.toHasSmul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) _inst_7) (Mul.toSMul.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_4)))] [_inst_9 : IsScalarTower.{u1, u3, u3} G M M (MulAction.toHasSmul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_5) (Mul.toSMul.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_4))) (MulAction.toHasSmul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_5)] [_inst_10 : IsScalarTower.{u2, u3, u3} H M M (MulAction.toHasSmul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) _inst_7) (Mul.toSMul.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_4))) (MulAction.toHasSmul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) _inst_7)] [_inst_11 : IsScalarTower.{u1, u2, u3} G H M _inst_1 (MulAction.toHasSmul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) _inst_7) (MulAction.toHasSmul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_5)], IsScalarTower.{u1, u2, u3} G H (Units.{u3} M _inst_4) _inst_1 (MulAction.toHasSmul.{u2, u3} H (Units.{u3} M _inst_4) (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) (Units.mulAction'.{u2, u3} H M _inst_3 _inst_4 _inst_7 _inst_8 _inst_10)) (MulAction.toHasSmul.{u1, u3} G (Units.{u3} M _inst_4) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Units.mulAction'.{u1, u3} G M _inst_2 _inst_4 _inst_5 _inst_6 _inst_9))
but is expected to have type
  forall {G : Type.{u1}} {H : Type.{u2}} {M : Type.{u3}} [_inst_1 : SMul.{u1, u2} G H] [_inst_2 : Group.{u1} G] [_inst_3 : Group.{u2} H] [_inst_4 : Monoid.{u3} M] [_inst_5 : MulAction.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_6 : SMulCommClass.{u1, u3, u3} G M M (MulAction.toSMul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_5) (MulAction.toSMul.{u3, u3} M M _inst_4 (Monoid.toMulAction.{u3} M _inst_4))] [_inst_7 : MulAction.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))] [_inst_8 : SMulCommClass.{u2, u3, u3} H M M (MulAction.toSMul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) _inst_7) (MulAction.toSMul.{u3, u3} M M _inst_4 (Monoid.toMulAction.{u3} M _inst_4))] [_inst_9 : IsScalarTower.{u1, u3, u3} G M M (MulAction.toSMul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_5) (MulAction.toSMul.{u3, u3} M M _inst_4 (Monoid.toMulAction.{u3} M _inst_4)) (MulAction.toSMul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_5)] [_inst_10 : IsScalarTower.{u2, u3, u3} H M M (MulAction.toSMul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) _inst_7) (MulAction.toSMul.{u3, u3} M M _inst_4 (Monoid.toMulAction.{u3} M _inst_4)) (MulAction.toSMul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) _inst_7)] [_inst_11 : IsScalarTower.{u1, u2, u3} G H M _inst_1 (MulAction.toSMul.{u2, u3} H M (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) _inst_7) (MulAction.toSMul.{u1, u3} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_5)], IsScalarTower.{u1, u2, u3} G H (Units.{u3} M _inst_4) _inst_1 (MulAction.toSMul.{u2, u3} H (Units.{u3} M _inst_4) (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) (Units.mulAction'.{u2, u3} H M _inst_3 _inst_4 _inst_7 _inst_8 _inst_10)) (MulAction.toSMul.{u1, u3} G (Units.{u3} M _inst_4) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Units.mulAction'.{u1, u3} G M _inst_2 _inst_4 _inst_5 _inst_6 _inst_9))
Case conversion may be inaccurate. Consider using '#align units.is_scalar_tower' Units.isScalarTower'ₓ'. -/
/-- Transfer `is_scalar_tower G H M` to `is_scalar_tower G H Mˣ` -/
instance isScalarTower' [SMul G H] [Group G] [Group H] [Monoid M] [MulAction G M]
    [SMulCommClass G M M] [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M]
    [IsScalarTower H M M] [IsScalarTower G H M] : IsScalarTower G H Mˣ
    where smul_assoc g h m := Units.ext <| smul_assoc g h (m : M)
#align units.is_scalar_tower' Units.isScalarTower'

/- warning: units.is_scalar_tower'_left -> Units.isScalarTower'_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {M : Type.{u2}} {α : Type.{u3}} [_inst_1 : Group.{u1} G] [_inst_2 : Monoid.{u2} M] [_inst_3 : MulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_4 : SMul.{u2, u3} M α] [_inst_5 : SMul.{u1, u3} G α] [_inst_6 : SMulCommClass.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)))] [_inst_7 : IsScalarTower.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))) (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3)] [_inst_8 : IsScalarTower.{u1, u2, u3} G M α (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) _inst_4 _inst_5], IsScalarTower.{u1, u2, u3} G (Units.{u2} M _inst_2) α (MulAction.toHasSmul.{u1, u2} G (Units.{u2} M _inst_2) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Units.mulAction'.{u1, u2} G M _inst_1 _inst_2 _inst_3 _inst_6 _inst_7)) (Units.hasSmul.{u2, u3} M α _inst_2 _inst_4) _inst_5
but is expected to have type
  forall {G : Type.{u1}} {M : Type.{u2}} {α : Type.{u3}} [_inst_1 : Group.{u1} G] [_inst_2 : Monoid.{u2} M] [_inst_3 : MulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_4 : SMul.{u2, u3} M α] [_inst_5 : SMul.{u1, u3} G α] [_inst_6 : SMulCommClass.{u1, u2, u2} G M M (MulAction.toSMul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (MulAction.toSMul.{u2, u2} M M _inst_2 (Monoid.toMulAction.{u2} M _inst_2))] [_inst_7 : IsScalarTower.{u1, u2, u2} G M M (MulAction.toSMul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (MulAction.toSMul.{u2, u2} M M _inst_2 (Monoid.toMulAction.{u2} M _inst_2)) (MulAction.toSMul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3)] [_inst_8 : IsScalarTower.{u1, u2, u3} G M α (MulAction.toSMul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) _inst_4 _inst_5], IsScalarTower.{u1, u2, u3} G (Units.{u2} M _inst_2) α (MulAction.toSMul.{u1, u2} G (Units.{u2} M _inst_2) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Units.mulAction'.{u1, u2} G M _inst_1 _inst_2 _inst_3 _inst_6 _inst_7)) (Units.instSMulUnits.{u2, u3} M α _inst_2 _inst_4) _inst_5
Case conversion may be inaccurate. Consider using '#align units.is_scalar_tower'_left Units.isScalarTower'_leftₓ'. -/
/-- Transfer `is_scalar_tower G M α` to `is_scalar_tower G Mˣ α` -/
instance isScalarTower'_left [Group G] [Monoid M] [MulAction G M] [SMul M α] [SMul G α]
    [SMulCommClass G M M] [IsScalarTower G M M] [IsScalarTower G M α] : IsScalarTower G Mˣ α
    where smul_assoc g m := (smul_assoc g (m : M) : _)
#align units.is_scalar_tower'_left Units.isScalarTower'_left

-- Just to prove this transfers a particularly useful instance.
example [Monoid M] [Monoid N] [MulAction M N] [SMulCommClass M N N] [IsScalarTower M N N] :
    MulAction Mˣ Nˣ :=
  Units.mulAction'

/- warning: units.mul_distrib_mul_action' -> Units.mulDistribMulAction' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {M : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Monoid.{u2} M] [_inst_3 : MulDistribMulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2] [_inst_4 : SMulCommClass.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (MulDistribMulAction.toMulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2 _inst_3)) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)))] [_inst_5 : IsScalarTower.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (MulDistribMulAction.toMulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2 _inst_3)) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))) (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (MulDistribMulAction.toMulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2 _inst_3))], MulDistribMulAction.{u1, u2} G (Units.{u2} M _inst_2) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (DivInvMonoid.toMonoid.{u2} (Units.{u2} M _inst_2) (Group.toDivInvMonoid.{u2} (Units.{u2} M _inst_2) (Units.group.{u2} M _inst_2)))
but is expected to have type
  forall {G : Type.{u1}} {M : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Monoid.{u2} M] [_inst_3 : MulDistribMulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2] [_inst_4 : SMulCommClass.{u1, u2, u2} G M M (MulAction.toSMul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (MulDistribMulAction.toMulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2 _inst_3)) (MulAction.toSMul.{u2, u2} M M _inst_2 (Monoid.toMulAction.{u2} M _inst_2))] [_inst_5 : IsScalarTower.{u1, u2, u2} G M M (MulAction.toSMul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (MulDistribMulAction.toMulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2 _inst_3)) (MulAction.toSMul.{u2, u2} M M _inst_2 (Monoid.toMulAction.{u2} M _inst_2)) (MulAction.toSMul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (MulDistribMulAction.toMulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2 _inst_3))], MulDistribMulAction.{u1, u2} G (Units.{u2} M _inst_2) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (DivInvMonoid.toMonoid.{u2} (Units.{u2} M _inst_2) (Group.toDivInvMonoid.{u2} (Units.{u2} M _inst_2) (Units.instGroupUnits.{u2} M _inst_2)))
Case conversion may be inaccurate. Consider using '#align units.mul_distrib_mul_action' Units.mulDistribMulAction'ₓ'. -/
/-- A stronger form of `units.mul_action'`. -/
instance mulDistribMulAction' [Group G] [Monoid M] [MulDistribMulAction G M] [SMulCommClass G M M]
    [IsScalarTower G M M] : MulDistribMulAction G Mˣ :=
  { Units.mulAction' with
    smul := (· • ·)
    smul_one := fun m => Units.ext <| smul_one _
    smul_mul := fun g m₁ m₂ => Units.ext <| smul_mul' _ _ _ }
#align units.mul_distrib_mul_action' Units.mulDistribMulAction'

end Units

/- warning: is_unit.smul -> IsUnit.smul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {M : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Monoid.{u2} M] [_inst_3 : MulAction.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_4 : SMulCommClass.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)))] [_inst_5 : IsScalarTower.{u1, u2, u2} G M M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))) (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3)] {m : M} (g : G), (IsUnit.{u2} M _inst_2 m) -> (IsUnit.{u2} M _inst_2 (SMul.smul.{u1, u2} G M (MulAction.toHasSmul.{u1, u2} G M (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) g m))
but is expected to have type
  forall {G : Type.{u2}} {M : Type.{u1}} [_inst_1 : Group.{u2} G] [_inst_2 : Monoid.{u1} M] [_inst_3 : MulAction.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))] [_inst_4 : SMulCommClass.{u2, u1, u1} G M M (MulAction.toSMul.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_3) (MulAction.toSMul.{u1, u1} M M _inst_2 (Monoid.toMulAction.{u1} M _inst_2))] [_inst_5 : IsScalarTower.{u2, u1, u1} G M M (MulAction.toSMul.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_3) (MulAction.toSMul.{u1, u1} M M _inst_2 (Monoid.toMulAction.{u1} M _inst_2)) (MulAction.toSMul.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_3)] {m : M} (g : G), (IsUnit.{u1} M _inst_2 m) -> (IsUnit.{u1} M _inst_2 (HSMul.hSMul.{u2, u1, u1} G M M (instHSMul.{u2, u1} G M (MulAction.toSMul.{u2, u1} G M (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_3)) g m))
Case conversion may be inaccurate. Consider using '#align is_unit.smul IsUnit.smulₓ'. -/
theorem IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨g • u, Units.val_smul _ _⟩
#align is_unit.smul IsUnit.smul

