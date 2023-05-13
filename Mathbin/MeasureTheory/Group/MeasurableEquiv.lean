/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module measure_theory.group.measurable_equiv
! leanprover-community/mathlib commit bd15ff41b70f5e2cc210f26f25a8d5c53b20d3de
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Group.Arithmetic

/-!
# (Scalar) multiplication and (vector) addition as measurable equivalences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the following measurable equivalences:

* `measurable_equiv.smul`: if a group `G` acts on `α` by measurable maps, then each element `c : G`
  defines a measurable automorphism of `α`;
* `measurable_equiv.vadd`: additive version of `measurable_equiv.smul`;
* `measurable_equiv.smul₀`: if a group with zero `G` acts on `α` by measurable maps, then each
  nonzero element `c : G` defines a measurable automorphism of `α`;
* `measurable_equiv.mul_left`: if `G` is a group with measurable multiplication, then left
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_left`: additive version of `measurable_equiv.mul_left`;
* `measurable_equiv.mul_right`: if `G` is a group with measurable multiplication, then right
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_right`: additive version of `measurable_equiv.mul_right`;
* `measurable_equiv.mul_left₀`, `measurable_equiv.mul_right₀`: versions of
  `measurable_equiv.mul_left` and `measurable_equiv.mul_right` for groups with zero;
* `measurable_equiv.inv`: `has_inv.inv` as a measurable automorphism
  of a group (or a group with zero);
* `measurable_equiv.neg`: negation as a measurable automorphism of an additive group.

We also deduce that the corresponding maps are measurable embeddings.

## Tags

measurable, equivalence, group action
-/


namespace MeasurableEquiv

variable {G G₀ α : Type _} [MeasurableSpace G] [MeasurableSpace G₀] [MeasurableSpace α] [Group G]
  [GroupWithZero G₀] [MulAction G α] [MulAction G₀ α] [MeasurableSMul G α] [MeasurableSMul G₀ α]

#print MeasurableEquiv.smul /-
/-- If a group `G` acts on `α` by measurable maps, then each element `c : G` defines a measurable
automorphism of `α`. -/
@[to_additive
      "If an additive group `G` acts on `α` by measurable maps, then each element `c : G`\ndefines a measurable automorphism of `α`.",
  simps (config := { fullyApplied := false }) toEquiv apply]
def smul (c : G) : α ≃ᵐ α where
  toEquiv := MulAction.toPerm c
  measurable_to_fun := measurable_const_smul c
  measurable_inv_fun := measurable_const_smul c⁻¹
#align measurable_equiv.smul MeasurableEquiv.smul
#align measurable_equiv.vadd MeasurableEquiv.vadd
-/

#print measurableEmbedding_const_smul /-
@[to_additive]
theorem measurableEmbedding_const_smul (c : G) : MeasurableEmbedding ((· • ·) c : α → α) :=
  (smul c).MeasurableEmbedding
#align measurable_embedding_const_smul measurableEmbedding_const_smul
#align measurable_embedding_const_vadd measurableEmbedding_const_vadd
-/

/- warning: measurable_equiv.symm_smul -> MeasurableEquiv.symm_smul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_3 : MeasurableSpace.{u2} α] [_inst_4 : Group.{u1} G] [_inst_6 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))] [_inst_8 : MeasurableSMul.{u1, u2} G α (MulAction.toHasSmul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) _inst_6) _inst_1 _inst_3] (c : G), Eq.{succ u2} (MeasurableEquiv.{u2, u2} α α _inst_3 _inst_3) (MeasurableEquiv.symm.{u2, u2} α α _inst_3 _inst_3 (MeasurableEquiv.smul.{u1, u2} G α _inst_1 _inst_3 _inst_4 _inst_6 _inst_8 c)) (MeasurableEquiv.smul.{u1, u2} G α _inst_1 _inst_3 _inst_4 _inst_6 _inst_8 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) c))
but is expected to have type
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_3 : MeasurableSpace.{u2} α] [_inst_4 : Group.{u1} G] [_inst_6 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))] [_inst_8 : MeasurableSMul.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) _inst_6) _inst_1 _inst_3] (c : G), Eq.{succ u2} (MeasurableEquiv.{u2, u2} α α _inst_3 _inst_3) (MeasurableEquiv.symm.{u2, u2} α α _inst_3 _inst_3 (MeasurableEquiv.smul.{u1, u2} G α _inst_1 _inst_3 _inst_4 _inst_6 _inst_8 c)) (MeasurableEquiv.smul.{u1, u2} G α _inst_1 _inst_3 _inst_4 _inst_6 _inst_8 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_4)))) c))
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_smul MeasurableEquiv.symm_smulₓ'. -/
@[simp, to_additive]
theorem symm_smul (c : G) : (smul c : α ≃ᵐ α).symm = smul c⁻¹ :=
  ext rfl
#align measurable_equiv.symm_smul MeasurableEquiv.symm_smul
#align measurable_equiv.symm_vadd MeasurableEquiv.symm_vadd

/- warning: measurable_equiv.smul₀ -> MeasurableEquiv.smul₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_3 : MeasurableSpace.{u2} α] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_7 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))] [_inst_9 : MeasurableSMul.{u1, u2} G₀ α (MulAction.toHasSmul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)) _inst_7) _inst_2 _inst_3] (c : G₀), (Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))) -> (MeasurableEquiv.{u2, u2} α α _inst_3 _inst_3)
but is expected to have type
  forall {G₀ : Type.{u1}} {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_3 : MeasurableSpace.{u2} α] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_7 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))] [_inst_9 : MeasurableSMul.{u1, u2} G₀ α (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)) _inst_7) _inst_2 _inst_3] (c : G₀), (Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) -> (MeasurableEquiv.{u2, u2} α α _inst_3 _inst_3)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.smul₀ MeasurableEquiv.smul₀ₓ'. -/
/-- If a group with zero `G₀` acts on `α` by measurable maps, then each nonzero element `c : G₀`
defines a measurable automorphism of `α` -/
def smul₀ (c : G₀) (hc : c ≠ 0) : α ≃ᵐ α :=
  MeasurableEquiv.smul (Units.mk0 c hc)
#align measurable_equiv.smul₀ MeasurableEquiv.smul₀

/- warning: measurable_equiv.coe_smul₀ -> MeasurableEquiv.coe_smul₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_3 : MeasurableSpace.{u2} α] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_7 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))] [_inst_9 : MeasurableSMul.{u1, u2} G₀ α (MulAction.toHasSmul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)) _inst_7) _inst_2 _inst_3] {c : G₀} (hc : Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))), Eq.{succ u2} (α -> α) (coeFn.{succ u2, succ u2} (MeasurableEquiv.{u2, u2} α α _inst_3 _inst_3) (fun (_x : MeasurableEquiv.{u2, u2} α α _inst_3 _inst_3) => α -> α) (MeasurableEquiv.hasCoeToFun.{u2, u2} α α _inst_3 _inst_3) (MeasurableEquiv.smul₀.{u1, u2} G₀ α _inst_2 _inst_3 _inst_5 _inst_7 _inst_9 c hc)) (SMul.smul.{u1, u2} G₀ α (MulAction.toHasSmul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)) _inst_7) c)
but is expected to have type
  forall {G₀ : Type.{u2}} {α : Type.{u1}} [_inst_2 : MeasurableSpace.{u2} G₀] [_inst_3 : MeasurableSpace.{u1} α] [_inst_5 : GroupWithZero.{u2} G₀] [_inst_7 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_5))] [_inst_9 : MeasurableSMul.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_5)) _inst_7) _inst_2 _inst_3] {c : G₀} (hc : Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_5))))), Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} α α _inst_3 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} α α _inst_3 _inst_3) α α (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} α α _inst_3 _inst_3) α α (MeasurableEquiv.instEquivLike.{u1, u1} α α _inst_3 _inst_3))) (MeasurableEquiv.smul₀.{u2, u1} G₀ α _inst_2 _inst_3 _inst_5 _inst_7 _inst_9 c hc)) ((fun (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.387 : G₀) (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.389 : α) => HSMul.hSMul.{u2, u1, u1} G₀ α α (instHSMul.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_5)) _inst_7)) x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.387 x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.389) c)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.coe_smul₀ MeasurableEquiv.coe_smul₀ₓ'. -/
@[simp]
theorem coe_smul₀ {c : G₀} (hc : c ≠ 0) : ⇑(smul₀ c hc : α ≃ᵐ α) = (· • ·) c :=
  rfl
#align measurable_equiv.coe_smul₀ MeasurableEquiv.coe_smul₀

/- warning: measurable_equiv.symm_smul₀ -> MeasurableEquiv.symm_smul₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_3 : MeasurableSpace.{u2} α] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_7 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))] [_inst_9 : MeasurableSMul.{u1, u2} G₀ α (MulAction.toHasSmul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)) _inst_7) _inst_2 _inst_3] {c : G₀} (hc : Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))), Eq.{succ u2} (MeasurableEquiv.{u2, u2} α α _inst_3 _inst_3) (MeasurableEquiv.symm.{u2, u2} α α _inst_3 _inst_3 (MeasurableEquiv.smul₀.{u1, u2} G₀ α _inst_2 _inst_3 _inst_5 _inst_7 _inst_9 c hc)) (MeasurableEquiv.smul₀.{u1, u2} G₀ α _inst_2 _inst_3 _inst_5 _inst_7 _inst_9 (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_5)) c) (inv_ne_zero.{u1} G₀ _inst_5 c hc))
but is expected to have type
  forall {G₀ : Type.{u2}} {α : Type.{u1}} [_inst_2 : MeasurableSpace.{u2} G₀] [_inst_3 : MeasurableSpace.{u1} α] [_inst_5 : GroupWithZero.{u2} G₀] [_inst_7 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_5))] [_inst_9 : MeasurableSMul.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_5)) _inst_7) _inst_2 _inst_3] {c : G₀} (hc : Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_5))))), Eq.{succ u1} (MeasurableEquiv.{u1, u1} α α _inst_3 _inst_3) (MeasurableEquiv.symm.{u1, u1} α α _inst_3 _inst_3 (MeasurableEquiv.smul₀.{u2, u1} G₀ α _inst_2 _inst_3 _inst_5 _inst_7 _inst_9 c hc)) (MeasurableEquiv.smul₀.{u2, u1} G₀ α _inst_2 _inst_3 _inst_5 _inst_7 _inst_9 (Inv.inv.{u2} G₀ (GroupWithZero.toInv.{u2} G₀ _inst_5) c) (inv_ne_zero.{u2} G₀ _inst_5 c hc))
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_smul₀ MeasurableEquiv.symm_smul₀ₓ'. -/
@[simp]
theorem symm_smul₀ {c : G₀} (hc : c ≠ 0) :
    (smul₀ c hc : α ≃ᵐ α).symm = smul₀ c⁻¹ (inv_ne_zero hc) :=
  ext rfl
#align measurable_equiv.symm_smul₀ MeasurableEquiv.symm_smul₀

/- warning: measurable_embedding_const_smul₀ -> measurableEmbedding_const_smul₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_3 : MeasurableSpace.{u2} α] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_7 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))] [_inst_9 : MeasurableSMul.{u1, u2} G₀ α (MulAction.toHasSmul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)) _inst_7) _inst_2 _inst_3] {c : G₀}, (Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))) -> (MeasurableEmbedding.{u2, u2} α α _inst_3 _inst_3 (SMul.smul.{u1, u2} G₀ α (MulAction.toHasSmul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)) _inst_7) c))
but is expected to have type
  forall {G₀ : Type.{u2}} {α : Type.{u1}} [_inst_2 : MeasurableSpace.{u2} G₀] [_inst_3 : MeasurableSpace.{u1} α] [_inst_5 : GroupWithZero.{u2} G₀] [_inst_7 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_5))] [_inst_9 : MeasurableSMul.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_5)) _inst_7) _inst_2 _inst_3] {c : G₀}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_5))))) -> (MeasurableEmbedding.{u1, u1} α α _inst_3 _inst_3 ((fun (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.520 : G₀) (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.522 : α) => HSMul.hSMul.{u2, u1, u1} G₀ α α (instHSMul.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_5)) _inst_7)) x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.520 x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.522) c))
Case conversion may be inaccurate. Consider using '#align measurable_embedding_const_smul₀ measurableEmbedding_const_smul₀ₓ'. -/
theorem measurableEmbedding_const_smul₀ {c : G₀} (hc : c ≠ 0) :
    MeasurableEmbedding ((· • ·) c : α → α) :=
  (smul₀ c hc).MeasurableEmbedding
#align measurable_embedding_const_smul₀ measurableEmbedding_const_smul₀

section Mul

variable [MeasurableMul G] [MeasurableMul G₀]

/- warning: measurable_equiv.mul_left -> MeasurableEquiv.mulLeft is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))], G -> (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))], G -> (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.mul_left MeasurableEquiv.mulLeftₓ'. -/
/-- If `G` is a group with measurable multiplication, then left multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive
      "If `G` is an additive group with measurable addition, then addition of `g : G`\non the left is a measurable automorphism of `G`."]
def mulLeft (g : G) : G ≃ᵐ G :=
  smul g
#align measurable_equiv.mul_left MeasurableEquiv.mulLeft
#align measurable_equiv.add_left MeasurableEquiv.addLeft

/- warning: measurable_equiv.coe_mul_left -> MeasurableEquiv.coe_mulLeft is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (G -> G) (coeFn.{succ u1, succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) (fun (_x : MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) => G -> G) (MeasurableEquiv.hasCoeToFun.{u1, u1} G G _inst_1 _inst_1) (MeasurableEquiv.mulLeft.{u1} G _inst_1 _inst_4 _inst_10 g)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))) g)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (forall (ᾰ : G), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => G) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) G (fun (_x : G) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => G) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) G G (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) G G (MeasurableEquiv.instEquivLike.{u1, u1} G G _inst_1 _inst_1))) (MeasurableEquiv.mulLeft.{u1} G _inst_1 _inst_4 _inst_10 g)) ((fun (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.690 : G) (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.692 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))) x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.690 x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.692) g)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.coe_mul_left MeasurableEquiv.coe_mulLeftₓ'. -/
@[simp, to_additive]
theorem coe_mulLeft (g : G) : ⇑(mulLeft g) = (· * ·) g :=
  rfl
#align measurable_equiv.coe_mul_left MeasurableEquiv.coe_mulLeft
#align measurable_equiv.coe_add_left MeasurableEquiv.coe_addLeft

/- warning: measurable_equiv.symm_mul_left -> MeasurableEquiv.symm_mulLeft is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) (MeasurableEquiv.symm.{u1, u1} G G _inst_1 _inst_1 (MeasurableEquiv.mulLeft.{u1} G _inst_1 _inst_4 _inst_10 g)) (MeasurableEquiv.mulLeft.{u1} G _inst_1 _inst_4 _inst_10 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) g))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) (MeasurableEquiv.symm.{u1, u1} G G _inst_1 _inst_1 (MeasurableEquiv.mulLeft.{u1} G _inst_1 _inst_4 _inst_10 g)) (MeasurableEquiv.mulLeft.{u1} G _inst_1 _inst_4 _inst_10 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_4)))) g))
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_mul_left MeasurableEquiv.symm_mulLeftₓ'. -/
@[simp, to_additive]
theorem symm_mulLeft (g : G) : (mulLeft g).symm = mulLeft g⁻¹ :=
  ext rfl
#align measurable_equiv.symm_mul_left MeasurableEquiv.symm_mulLeft
#align measurable_equiv.symm_add_left MeasurableEquiv.symm_addLeft

/- warning: measurable_equiv.to_equiv_mul_left -> MeasurableEquiv.toEquiv_mulLeft is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (MeasurableEquiv.toEquiv.{u1, u1} G G _inst_1 _inst_1 (MeasurableEquiv.mulLeft.{u1} G _inst_1 _inst_4 _inst_10 g)) (Equiv.mulLeft.{u1} G _inst_4 g)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (MeasurableEquiv.toEquiv.{u1, u1} G G _inst_1 _inst_1 (MeasurableEquiv.mulLeft.{u1} G _inst_1 _inst_4 _inst_10 g)) (Equiv.mulLeft.{u1} G _inst_4 g)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.to_equiv_mul_left MeasurableEquiv.toEquiv_mulLeftₓ'. -/
@[simp, to_additive]
theorem toEquiv_mulLeft (g : G) : (mulLeft g).toEquiv = Equiv.mulLeft g :=
  rfl
#align measurable_equiv.to_equiv_mul_left MeasurableEquiv.toEquiv_mulLeft
#align measurable_equiv.to_equiv_add_left MeasurableEquiv.toEquiv_addLeft

/- warning: measurable_embedding_mul_left -> measurableEmbedding_mulLeft is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), MeasurableEmbedding.{u1, u1} G G _inst_1 _inst_1 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))) g)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), MeasurableEmbedding.{u1, u1} G G _inst_1 _inst_1 ((fun (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.869 : G) (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.871 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))) x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.869 x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.871) g)
Case conversion may be inaccurate. Consider using '#align measurable_embedding_mul_left measurableEmbedding_mulLeftₓ'. -/
@[to_additive]
theorem measurableEmbedding_mulLeft (g : G) : MeasurableEmbedding ((· * ·) g) :=
  (mulLeft g).MeasurableEmbedding
#align measurable_embedding_mul_left measurableEmbedding_mulLeft
#align measurable_embedding_add_left measurableEmbedding_addLeft

/- warning: measurable_equiv.mul_right -> MeasurableEquiv.mulRight is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))], G -> (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))], G -> (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.mul_right MeasurableEquiv.mulRightₓ'. -/
/-- If `G` is a group with measurable multiplication, then right multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive
      "If `G` is an additive group with measurable addition, then addition of `g : G`\non the right is a measurable automorphism of `G`."]
def mulRight (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.mulRight g
  measurable_to_fun := measurable_mul_const g
  measurable_inv_fun := measurable_mul_const g⁻¹
#align measurable_equiv.mul_right MeasurableEquiv.mulRight
#align measurable_equiv.add_right MeasurableEquiv.addRight

/- warning: measurable_embedding_mul_right -> measurableEmbedding_mulRight is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), MeasurableEmbedding.{u1, u1} G G _inst_1 _inst_1 (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))) x g)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), MeasurableEmbedding.{u1, u1} G G _inst_1 _inst_1 (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))) x g)
Case conversion may be inaccurate. Consider using '#align measurable_embedding_mul_right measurableEmbedding_mulRightₓ'. -/
@[to_additive]
theorem measurableEmbedding_mulRight (g : G) : MeasurableEmbedding fun x => x * g :=
  (mulRight g).MeasurableEmbedding
#align measurable_embedding_mul_right measurableEmbedding_mulRight
#align measurable_embedding_add_right measurableEmbedding_addRight

/- warning: measurable_equiv.coe_mul_right -> MeasurableEquiv.coe_mulRight is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (G -> G) (coeFn.{succ u1, succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) (fun (_x : MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) => G -> G) (MeasurableEquiv.hasCoeToFun.{u1, u1} G G _inst_1 _inst_1) (MeasurableEquiv.mulRight.{u1} G _inst_1 _inst_4 _inst_10 g)) (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))) x g)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (forall (ᾰ : G), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => G) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) G (fun (_x : G) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => G) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) G G (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) G G (MeasurableEquiv.instEquivLike.{u1, u1} G G _inst_1 _inst_1))) (MeasurableEquiv.mulRight.{u1} G _inst_1 _inst_4 _inst_10 g)) (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))) x g)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.coe_mul_right MeasurableEquiv.coe_mulRightₓ'. -/
@[simp, to_additive]
theorem coe_mulRight (g : G) : ⇑(mulRight g) = fun x => x * g :=
  rfl
#align measurable_equiv.coe_mul_right MeasurableEquiv.coe_mulRight
#align measurable_equiv.coe_add_right MeasurableEquiv.coe_addRight

/- warning: measurable_equiv.symm_mul_right -> MeasurableEquiv.symm_mulRight is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) (MeasurableEquiv.symm.{u1, u1} G G _inst_1 _inst_1 (MeasurableEquiv.mulRight.{u1} G _inst_1 _inst_4 _inst_10 g)) (MeasurableEquiv.mulRight.{u1} G _inst_1 _inst_4 _inst_10 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) g))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1) (MeasurableEquiv.symm.{u1, u1} G G _inst_1 _inst_1 (MeasurableEquiv.mulRight.{u1} G _inst_1 _inst_4 _inst_10 g)) (MeasurableEquiv.mulRight.{u1} G _inst_1 _inst_4 _inst_10 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_4)))) g))
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_mul_right MeasurableEquiv.symm_mulRightₓ'. -/
@[simp, to_additive]
theorem symm_mulRight (g : G) : (mulRight g).symm = mulRight g⁻¹ :=
  ext rfl
#align measurable_equiv.symm_mul_right MeasurableEquiv.symm_mulRight
#align measurable_equiv.symm_add_right MeasurableEquiv.symm_addRight

/- warning: measurable_equiv.to_equiv_mul_right -> MeasurableEquiv.toEquiv_mulRight is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (MeasurableEquiv.toEquiv.{u1, u1} G G _inst_1 _inst_1 (MeasurableEquiv.mulRight.{u1} G _inst_1 _inst_4 _inst_10 g)) (Equiv.mulRight.{u1} G _inst_4 g)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] (g : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (MeasurableEquiv.toEquiv.{u1, u1} G G _inst_1 _inst_1 (MeasurableEquiv.mulRight.{u1} G _inst_1 _inst_4 _inst_10 g)) (Equiv.mulRight.{u1} G _inst_4 g)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.to_equiv_mul_right MeasurableEquiv.toEquiv_mulRightₓ'. -/
@[simp, to_additive]
theorem toEquiv_mulRight (g : G) : (mulRight g).toEquiv = Equiv.mulRight g :=
  rfl
#align measurable_equiv.to_equiv_mul_right MeasurableEquiv.toEquiv_mulRight
#align measurable_equiv.to_equiv_add_right MeasurableEquiv.toEquiv_addRight

/- warning: measurable_equiv.mul_left₀ -> MeasurableEquiv.mulLeft₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] (g : G₀), (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))) -> (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] (g : G₀), (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) -> (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.mul_left₀ MeasurableEquiv.mulLeft₀ₓ'. -/
/-- If `G₀` is a group with zero with measurable multiplication, then left multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
def mulLeft₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀ :=
  smul₀ g hg
#align measurable_equiv.mul_left₀ MeasurableEquiv.mulLeft₀

/- warning: measurable_embedding_mul_left₀ -> measurableEmbedding_mulLeft₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀}, (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))) -> (MeasurableEmbedding.{u1, u1} G₀ G₀ _inst_2 _inst_2 (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) g))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀}, (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) -> (MeasurableEmbedding.{u1, u1} G₀ G₀ _inst_2 _inst_2 ((fun (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.1296 : G₀) (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.1298 : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.1296 x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.1298) g))
Case conversion may be inaccurate. Consider using '#align measurable_embedding_mul_left₀ measurableEmbedding_mulLeft₀ₓ'. -/
theorem measurableEmbedding_mulLeft₀ {g : G₀} (hg : g ≠ 0) : MeasurableEmbedding ((· * ·) g) :=
  (mulLeft₀ g hg).MeasurableEmbedding
#align measurable_embedding_mul_left₀ measurableEmbedding_mulLeft₀

/- warning: measurable_equiv.coe_mul_left₀ -> MeasurableEquiv.coe_mulLeft₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))), Eq.{succ u1} (G₀ -> G₀) (coeFn.{succ u1, succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) (fun (_x : MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) => G₀ -> G₀) (MeasurableEquiv.hasCoeToFun.{u1, u1} G₀ G₀ _inst_2 _inst_2) (MeasurableEquiv.mulLeft₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) g)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))), Eq.{succ u1} (forall (ᾰ : G₀), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G₀) => G₀) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) G₀ (fun (_x : G₀) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G₀) => G₀) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) G₀ G₀ (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) G₀ G₀ (MeasurableEquiv.instEquivLike.{u1, u1} G₀ G₀ _inst_2 _inst_2))) (MeasurableEquiv.mulLeft₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) ((fun (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.1377 : G₀) (x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.1379 : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.1377 x._@.Mathlib.MeasureTheory.Group.MeasurableEquiv._hyg.1379) g)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.coe_mul_left₀ MeasurableEquiv.coe_mulLeft₀ₓ'. -/
@[simp]
theorem coe_mulLeft₀ {g : G₀} (hg : g ≠ 0) : ⇑(mulLeft₀ g hg) = (· * ·) g :=
  rfl
#align measurable_equiv.coe_mul_left₀ MeasurableEquiv.coe_mulLeft₀

/- warning: measurable_equiv.symm_mul_left₀ -> MeasurableEquiv.symm_mulLeft₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))), Eq.{succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) (MeasurableEquiv.symm.{u1, u1} G₀ G₀ _inst_2 _inst_2 (MeasurableEquiv.mulLeft₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) (MeasurableEquiv.mulLeft₀.{u1} G₀ _inst_2 _inst_5 _inst_11 (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_5)) g) (inv_ne_zero.{u1} G₀ _inst_5 g hg))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))), Eq.{succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) (MeasurableEquiv.symm.{u1, u1} G₀ G₀ _inst_2 _inst_2 (MeasurableEquiv.mulLeft₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) (MeasurableEquiv.mulLeft₀.{u1} G₀ _inst_2 _inst_5 _inst_11 (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_5) g) (inv_ne_zero.{u1} G₀ _inst_5 g hg))
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_mul_left₀ MeasurableEquiv.symm_mulLeft₀ₓ'. -/
@[simp]
theorem symm_mulLeft₀ {g : G₀} (hg : g ≠ 0) :
    (mulLeft₀ g hg).symm = mulLeft₀ g⁻¹ (inv_ne_zero hg) :=
  ext rfl
#align measurable_equiv.symm_mul_left₀ MeasurableEquiv.symm_mulLeft₀

/- warning: measurable_equiv.to_equiv_mul_left₀ -> MeasurableEquiv.toEquiv_mulLeft₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))), Eq.{succ u1} (Equiv.{succ u1, succ u1} G₀ G₀) (MeasurableEquiv.toEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2 (MeasurableEquiv.mulLeft₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) (Equiv.mulLeft₀.{u1} G₀ _inst_5 g hg)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))), Eq.{succ u1} (Equiv.{succ u1, succ u1} G₀ G₀) (MeasurableEquiv.toEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2 (MeasurableEquiv.mulLeft₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) (Equiv.mulLeft₀.{u1} G₀ _inst_5 g hg)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.to_equiv_mul_left₀ MeasurableEquiv.toEquiv_mulLeft₀ₓ'. -/
@[simp]
theorem toEquiv_mulLeft₀ {g : G₀} (hg : g ≠ 0) : (mulLeft₀ g hg).toEquiv = Equiv.mulLeft₀ g hg :=
  rfl
#align measurable_equiv.to_equiv_mul_left₀ MeasurableEquiv.toEquiv_mulLeft₀

/- warning: measurable_equiv.mul_right₀ -> MeasurableEquiv.mulRight₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] (g : G₀), (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))) -> (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] (g : G₀), (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) -> (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.mul_right₀ MeasurableEquiv.mulRight₀ₓ'. -/
/-- If `G₀` is a group with zero with measurable multiplication, then right multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
def mulRight₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀
    where
  toEquiv := Equiv.mulRight₀ g hg
  measurable_to_fun := measurable_mul_const g
  measurable_inv_fun := measurable_mul_const g⁻¹
#align measurable_equiv.mul_right₀ MeasurableEquiv.mulRight₀

/- warning: measurable_embedding_mul_right₀ -> measurableEmbedding_mulRight₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀}, (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))) -> (MeasurableEmbedding.{u1, u1} G₀ G₀ _inst_2 _inst_2 (fun (x : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) x g))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀}, (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) -> (MeasurableEmbedding.{u1, u1} G₀ G₀ _inst_2 _inst_2 (fun (x : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) x g))
Case conversion may be inaccurate. Consider using '#align measurable_embedding_mul_right₀ measurableEmbedding_mulRight₀ₓ'. -/
theorem measurableEmbedding_mulRight₀ {g : G₀} (hg : g ≠ 0) : MeasurableEmbedding fun x => x * g :=
  (mulRight₀ g hg).MeasurableEmbedding
#align measurable_embedding_mul_right₀ measurableEmbedding_mulRight₀

/- warning: measurable_equiv.coe_mul_right₀ -> MeasurableEquiv.coe_mulRight₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))), Eq.{succ u1} (G₀ -> G₀) (coeFn.{succ u1, succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) (fun (_x : MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) => G₀ -> G₀) (MeasurableEquiv.hasCoeToFun.{u1, u1} G₀ G₀ _inst_2 _inst_2) (MeasurableEquiv.mulRight₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) (fun (x : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) x g)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))), Eq.{succ u1} (forall (ᾰ : G₀), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G₀) => G₀) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) G₀ (fun (_x : G₀) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G₀) => G₀) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) G₀ G₀ (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) G₀ G₀ (MeasurableEquiv.instEquivLike.{u1, u1} G₀ G₀ _inst_2 _inst_2))) (MeasurableEquiv.mulRight₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) (fun (x : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))) x g)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.coe_mul_right₀ MeasurableEquiv.coe_mulRight₀ₓ'. -/
@[simp]
theorem coe_mulRight₀ {g : G₀} (hg : g ≠ 0) : ⇑(mulRight₀ g hg) = fun x => x * g :=
  rfl
#align measurable_equiv.coe_mul_right₀ MeasurableEquiv.coe_mulRight₀

/- warning: measurable_equiv.symm_mul_right₀ -> MeasurableEquiv.symm_mulRight₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))), Eq.{succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) (MeasurableEquiv.symm.{u1, u1} G₀ G₀ _inst_2 _inst_2 (MeasurableEquiv.mulRight₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) (MeasurableEquiv.mulRight₀.{u1} G₀ _inst_2 _inst_5 _inst_11 (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_5)) g) (inv_ne_zero.{u1} G₀ _inst_5 g hg))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))), Eq.{succ u1} (MeasurableEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2) (MeasurableEquiv.symm.{u1, u1} G₀ G₀ _inst_2 _inst_2 (MeasurableEquiv.mulRight₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) (MeasurableEquiv.mulRight₀.{u1} G₀ _inst_2 _inst_5 _inst_11 (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_5) g) (inv_ne_zero.{u1} G₀ _inst_5 g hg))
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_mul_right₀ MeasurableEquiv.symm_mulRight₀ₓ'. -/
@[simp]
theorem symm_mulRight₀ {g : G₀} (hg : g ≠ 0) :
    (mulRight₀ g hg).symm = mulRight₀ g⁻¹ (inv_ne_zero hg) :=
  ext rfl
#align measurable_equiv.symm_mul_right₀ MeasurableEquiv.symm_mulRight₀

/- warning: measurable_equiv.to_equiv_mul_right₀ -> MeasurableEquiv.toEquiv_mulRight₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5)))))))), Eq.{succ u1} (Equiv.{succ u1, succ u1} G₀ G₀) (MeasurableEquiv.toEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2 (MeasurableEquiv.mulRight₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) (Equiv.mulRight₀.{u1} G₀ _inst_5 g hg)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} G₀] [_inst_5 : GroupWithZero.{u1} G₀] [_inst_11 : MeasurableMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))] {g : G₀} (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_5))))), Eq.{succ u1} (Equiv.{succ u1, succ u1} G₀ G₀) (MeasurableEquiv.toEquiv.{u1, u1} G₀ G₀ _inst_2 _inst_2 (MeasurableEquiv.mulRight₀.{u1} G₀ _inst_2 _inst_5 _inst_11 g hg)) (Equiv.mulRight₀.{u1} G₀ _inst_5 g hg)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.to_equiv_mul_right₀ MeasurableEquiv.toEquiv_mulRight₀ₓ'. -/
@[simp]
theorem toEquiv_mulRight₀ {g : G₀} (hg : g ≠ 0) : (mulRight₀ g hg).toEquiv = Equiv.mulRight₀ g hg :=
  rfl
#align measurable_equiv.to_equiv_mul_right₀ MeasurableEquiv.toEquiv_mulRight₀

end Mul

/- warning: measurable_equiv.inv -> MeasurableEquiv.inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_10 : MeasurableSpace.{u1} G] [_inst_11 : InvolutiveInv.{u1} G] [_inst_12 : MeasurableInv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_11) _inst_10], MeasurableEquiv.{u1, u1} G G _inst_10 _inst_10
but is expected to have type
  forall (G : Type.{u1}) [_inst_10 : MeasurableSpace.{u1} G] [_inst_11 : InvolutiveInv.{u1} G] [_inst_12 : MeasurableInv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_11) _inst_10], MeasurableEquiv.{u1, u1} G G _inst_10 _inst_10
Case conversion may be inaccurate. Consider using '#align measurable_equiv.inv MeasurableEquiv.invₓ'. -/
/-- Inversion as a measurable automorphism of a group or group with zero. -/
@[to_additive "Negation as a measurable automorphism of an additive group.",
  simps (config := { fullyApplied := false }) toEquiv apply]
def inv (G) [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] : G ≃ᵐ G
    where
  toEquiv := Equiv.inv G
  measurable_to_fun := measurable_inv
  measurable_inv_fun := measurable_inv
#align measurable_equiv.inv MeasurableEquiv.inv
#align measurable_equiv.neg MeasurableEquiv.neg

/- warning: measurable_equiv.symm_inv -> MeasurableEquiv.symm_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_10 : MeasurableSpace.{u1} G] [_inst_11 : InvolutiveInv.{u1} G] [_inst_12 : MeasurableInv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_11) _inst_10], Eq.{succ u1} (MeasurableEquiv.{u1, u1} G G _inst_10 _inst_10) (MeasurableEquiv.symm.{u1, u1} G G _inst_10 _inst_10 (MeasurableEquiv.inv.{u1} G _inst_10 _inst_11 _inst_12)) (MeasurableEquiv.inv.{u1} G _inst_10 _inst_11 _inst_12)
but is expected to have type
  forall {G : Type.{u1}} [_inst_10 : MeasurableSpace.{u1} G] [_inst_11 : InvolutiveInv.{u1} G] [_inst_12 : MeasurableInv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_11) _inst_10], Eq.{succ u1} (MeasurableEquiv.{u1, u1} G G _inst_10 _inst_10) (MeasurableEquiv.symm.{u1, u1} G G _inst_10 _inst_10 (MeasurableEquiv.inv.{u1} G _inst_10 _inst_11 _inst_12)) (MeasurableEquiv.inv.{u1} G _inst_10 _inst_11 _inst_12)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_inv MeasurableEquiv.symm_invₓ'. -/
@[simp, to_additive]
theorem symm_inv {G} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] :
    (inv G).symm = inv G :=
  rfl
#align measurable_equiv.symm_inv MeasurableEquiv.symm_inv
#align measurable_equiv.symm_neg MeasurableEquiv.symm_neg

/- warning: measurable_equiv.div_right -> MeasurableEquiv.divRight is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))], G -> (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))], G -> (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.div_right MeasurableEquiv.divRightₓ'. -/
/-- `equiv.div_right` as a `measurable_equiv`. -/
@[to_additive " `equiv.sub_right` as a `measurable_equiv` "]
def divRight [MeasurableMul G] (g : G) : G ≃ᵐ G
    where
  toEquiv := Equiv.divRight g
  measurable_to_fun := measurable_div_const' g
  measurable_inv_fun := measurable_mul_const g
#align measurable_equiv.div_right MeasurableEquiv.divRight
#align measurable_equiv.sub_right MeasurableEquiv.subRight

/- warning: measurable_equiv.div_left -> MeasurableEquiv.divLeft is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] [_inst_11 : MeasurableInv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) _inst_1], G -> (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_4 : Group.{u1} G] [_inst_10 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))] [_inst_11 : MeasurableInv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_4)))) _inst_1], G -> (MeasurableEquiv.{u1, u1} G G _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.div_left MeasurableEquiv.divLeftₓ'. -/
/-- `equiv.div_left` as a `measurable_equiv` -/
@[to_additive " `equiv.sub_left` as a `measurable_equiv` "]
def divLeft [MeasurableMul G] [MeasurableInv G] (g : G) : G ≃ᵐ G
    where
  toEquiv := Equiv.divLeft g
  measurable_to_fun := measurable_id.const_div g
  measurable_inv_fun := measurable_inv.mul_const g
#align measurable_equiv.div_left MeasurableEquiv.divLeft
#align measurable_equiv.sub_left MeasurableEquiv.subLeft

end MeasurableEquiv

