/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alex J. Best

! This file was ported from Lean 3 source module measure_theory.group.pointwise
! leanprover-community/mathlib commit bd15ff41b70f5e2cc210f26f25a8d5c53b20d3de
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Group.Arithmetic

/-!
# Pointwise set operations on `measurable_set`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove several versions of the following fact: if `s` is a measurable set, then so is
`a • s`. Note that the pointwise product of two measurable sets need not be measurable, so there is
no `measurable_set.mul` etc.
-/


open Pointwise

open Set

/- warning: measurable_set.const_smul -> MeasurableSet.const_smul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_3 : MeasurableSpace.{u1} G] [_inst_4 : MeasurableSpace.{u2} α] [_inst_5 : MeasurableSMul.{u1, u2} G α (MulAction.toHasSmul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2) _inst_3 _inst_4] {s : Set.{u2} α}, (MeasurableSet.{u2} α _inst_4 s) -> (forall (a : G), MeasurableSet.{u2} α _inst_4 (SMul.smul.{u1, u2} G (Set.{u2} α) (Set.smulSet.{u1, u2} G α (MulAction.toHasSmul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2)) a s))
but is expected to have type
  forall {G : Type.{u2}} {α : Type.{u1}} [_inst_1 : Group.{u2} G] [_inst_2 : MulAction.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))] [_inst_3 : MeasurableSpace.{u2} G] [_inst_4 : MeasurableSpace.{u1} α] [_inst_5 : MeasurableSMul.{u2, u1} G α (MulAction.toSMul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_2) _inst_3 _inst_4] {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_4 s) -> (forall (a : G), MeasurableSet.{u1} α _inst_4 (HSMul.hSMul.{u2, u1, u1} G (Set.{u1} α) (Set.{u1} α) (instHSMul.{u2, u1} G (Set.{u1} α) (Set.smulSet.{u2, u1} G α (MulAction.toSMul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_2))) a s))
Case conversion may be inaccurate. Consider using '#align measurable_set.const_smul MeasurableSet.const_smulₓ'. -/
@[to_additive]
theorem MeasurableSet.const_smul {G α : Type _} [Group G] [MulAction G α] [MeasurableSpace G]
    [MeasurableSpace α] [MeasurableSMul G α] {s : Set α} (hs : MeasurableSet s) (a : G) :
    MeasurableSet (a • s) := by
  rw [← preimage_smul_inv]
  exact measurable_const_smul _ hs
#align measurable_set.const_smul MeasurableSet.const_smul
#align measurable_set.const_vadd MeasurableSet.const_vadd

/- warning: measurable_set.const_smul_of_ne_zero -> MeasurableSet.const_smul_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} {α : Type.{u2}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))] [_inst_3 : MeasurableSpace.{u1} G₀] [_inst_4 : MeasurableSpace.{u2} α] [_inst_5 : MeasurableSMul.{u1, u2} G₀ α (MulAction.toHasSmul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) _inst_2) _inst_3 _inst_4] {s : Set.{u2} α}, (MeasurableSet.{u2} α _inst_4 s) -> (forall {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (MeasurableSet.{u2} α _inst_4 (SMul.smul.{u1, u2} G₀ (Set.{u2} α) (Set.smulSet.{u1, u2} G₀ α (MulAction.toHasSmul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) _inst_2)) a s)))
but is expected to have type
  forall {G₀ : Type.{u2}} {α : Type.{u1}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))] [_inst_3 : MeasurableSpace.{u2} G₀] [_inst_4 : MeasurableSpace.{u1} α] [_inst_5 : MeasurableSMul.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) _inst_2) _inst_3 _inst_4] {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_4 s) -> (forall {a : G₀}, (Ne.{succ u2} G₀ a (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))) -> (MeasurableSet.{u1} α _inst_4 (HSMul.hSMul.{u2, u1, u1} G₀ (Set.{u1} α) (Set.{u1} α) (instHSMul.{u2, u1} G₀ (Set.{u1} α) (Set.smulSet.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) _inst_2))) a s)))
Case conversion may be inaccurate. Consider using '#align measurable_set.const_smul_of_ne_zero MeasurableSet.const_smul_of_ne_zeroₓ'. -/
theorem MeasurableSet.const_smul_of_ne_zero {G₀ α : Type _} [GroupWithZero G₀] [MulAction G₀ α]
    [MeasurableSpace G₀] [MeasurableSpace α] [MeasurableSMul G₀ α] {s : Set α}
    (hs : MeasurableSet s) {a : G₀} (ha : a ≠ 0) : MeasurableSet (a • s) :=
  by
  rw [← preimage_smul_inv₀ ha]
  exact measurable_const_smul _ hs
#align measurable_set.const_smul_of_ne_zero MeasurableSet.const_smul_of_ne_zero

/- warning: measurable_set.const_smul₀ -> MeasurableSet.const_smul₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} {α : Type.{u2}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : Zero.{u2} α] [_inst_3 : MulActionWithZero.{u1, u2} G₀ α (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1) _inst_2] [_inst_4 : MeasurableSpace.{u1} G₀] [_inst_5 : MeasurableSpace.{u2} α] [_inst_6 : MeasurableSMul.{u1, u2} G₀ α (SMulZeroClass.toHasSmul.{u1, u2} G₀ α _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} G₀ α (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) _inst_2 (MulActionWithZero.toSMulWithZero.{u1, u2} G₀ α (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1) _inst_2 _inst_3))) _inst_4 _inst_5] [_inst_7 : MeasurableSingletonClass.{u2} α _inst_5] {s : Set.{u2} α}, (MeasurableSet.{u2} α _inst_5 s) -> (forall (a : G₀), MeasurableSet.{u2} α _inst_5 (SMul.smul.{u1, u2} G₀ (Set.{u2} α) (Set.smulSet.{u1, u2} G₀ α (SMulZeroClass.toHasSmul.{u1, u2} G₀ α _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} G₀ α (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) _inst_2 (MulActionWithZero.toSMulWithZero.{u1, u2} G₀ α (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1) _inst_2 _inst_3)))) a s))
but is expected to have type
  forall {G₀ : Type.{u2}} {α : Type.{u1}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : Zero.{u1} α] [_inst_3 : MulActionWithZero.{u2, u1} G₀ α (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1) _inst_2] [_inst_4 : MeasurableSpace.{u2} G₀] [_inst_5 : MeasurableSpace.{u1} α] [_inst_6 : MeasurableSMul.{u2, u1} G₀ α (SMulZeroClass.toSMul.{u2, u1} G₀ α _inst_2 (SMulWithZero.toSMulZeroClass.{u2, u1} G₀ α (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) _inst_2 (MulActionWithZero.toSMulWithZero.{u2, u1} G₀ α (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1) _inst_2 _inst_3))) _inst_4 _inst_5] [_inst_7 : MeasurableSingletonClass.{u1} α _inst_5] {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_5 s) -> (forall (a : G₀), MeasurableSet.{u1} α _inst_5 (HSMul.hSMul.{u2, u1, u1} G₀ (Set.{u1} α) (Set.{u1} α) (instHSMul.{u2, u1} G₀ (Set.{u1} α) (Set.smulSet.{u2, u1} G₀ α (SMulZeroClass.toSMul.{u2, u1} G₀ α _inst_2 (SMulWithZero.toSMulZeroClass.{u2, u1} G₀ α (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) _inst_2 (MulActionWithZero.toSMulWithZero.{u2, u1} G₀ α (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1) _inst_2 _inst_3))))) a s))
Case conversion may be inaccurate. Consider using '#align measurable_set.const_smul₀ MeasurableSet.const_smul₀ₓ'. -/
theorem MeasurableSet.const_smul₀ {G₀ α : Type _} [GroupWithZero G₀] [Zero α]
    [MulActionWithZero G₀ α] [MeasurableSpace G₀] [MeasurableSpace α] [MeasurableSMul G₀ α]
    [MeasurableSingletonClass α] {s : Set α} (hs : MeasurableSet s) (a : G₀) :
    MeasurableSet (a • s) := by
  rcases eq_or_ne a 0 with (rfl | ha)
  exacts[(subsingleton_zero_smul_set s).MeasurableSet, hs.const_smul_of_ne_zero ha]
#align measurable_set.const_smul₀ MeasurableSet.const_smul₀

