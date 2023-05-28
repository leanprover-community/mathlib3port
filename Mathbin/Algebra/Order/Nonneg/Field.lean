/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module algebra.order.nonneg.field
! leanprover-community/mathlib commit b3f4f007a962e3787aa0f3b5c7942a1317f7d88e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Field.Basic
import Mathbin.Algebra.Order.Field.Canonical.Defs
import Mathbin.Algebra.Order.Field.InjSurj
import Mathbin.Algebra.Order.Nonneg.Ring

/-!
# Semifield structure on the type of nonnegative elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.

## Main declarations

* `{x : α // 0 ≤ x}` is a `canonically_linear_ordered_semifield` if `α` is a `linear_ordered_field`.
-/


open Set

variable {α : Type _}

namespace Nonneg

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] {x y : α}

/- warning: nonneg.has_inv -> Nonneg.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α], Inv.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))))))) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α], Inv.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedSemiring.toPartialOrder.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))) x))
Case conversion may be inaccurate. Consider using '#align nonneg.has_inv Nonneg.invₓ'. -/
instance inv : Inv { x : α // 0 ≤ x } :=
  ⟨fun x => ⟨x⁻¹, inv_nonneg.2 x.2⟩⟩
#align nonneg.has_inv Nonneg.inv

/- warning: nonneg.coe_inv -> Nonneg.coe_inv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align nonneg.coe_inv Nonneg.coe_invₓ'. -/
@[simp, norm_cast]
protected theorem coe_inv (a : { x : α // 0 ≤ x }) : ((a⁻¹ : { x : α // 0 ≤ x }) : α) = a⁻¹ :=
  rfl
#align nonneg.coe_inv Nonneg.coe_inv

/- warning: nonneg.inv_mk -> Nonneg.inv_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align nonneg.inv_mk Nonneg.inv_mkₓ'. -/
@[simp]
theorem inv_mk (hx : 0 ≤ x) : (⟨x, hx⟩ : { x : α // 0 ≤ x })⁻¹ = ⟨x⁻¹, inv_nonneg.2 hx⟩ :=
  rfl
#align nonneg.inv_mk Nonneg.inv_mk

/- warning: nonneg.has_div -> Nonneg.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α], Div.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))))))) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α], Div.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedSemiring.toPartialOrder.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))) x))
Case conversion may be inaccurate. Consider using '#align nonneg.has_div Nonneg.divₓ'. -/
instance div : Div { x : α // 0 ≤ x } :=
  ⟨fun x y => ⟨x / y, div_nonneg x.2 y.2⟩⟩
#align nonneg.has_div Nonneg.div

/- warning: nonneg.coe_div -> Nonneg.coe_div is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align nonneg.coe_div Nonneg.coe_divₓ'. -/
@[simp, norm_cast]
protected theorem coe_div (a b : { x : α // 0 ≤ x }) : ((a / b : { x : α // 0 ≤ x }) : α) = a / b :=
  rfl
#align nonneg.coe_div Nonneg.coe_div

/- warning: nonneg.mk_div_mk -> Nonneg.mk_div_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align nonneg.mk_div_mk Nonneg.mk_div_mkₓ'. -/
@[simp]
theorem mk_div_mk (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
  rfl
#align nonneg.mk_div_mk Nonneg.mk_div_mk

/- warning: nonneg.has_zpow -> Nonneg.zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α], Pow.{u1, 0} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))))))) x)) Int
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α], Pow.{u1, 0} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedSemiring.toPartialOrder.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))) x)) Int
Case conversion may be inaccurate. Consider using '#align nonneg.has_zpow Nonneg.zpowₓ'. -/
instance zpow : Pow { x : α // 0 ≤ x } ℤ :=
  ⟨fun a n => ⟨a ^ n, zpow_nonneg a.2 _⟩⟩
#align nonneg.has_zpow Nonneg.zpow

/- warning: nonneg.coe_zpow -> Nonneg.coe_zpow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align nonneg.coe_zpow Nonneg.coe_zpowₓ'. -/
@[simp, norm_cast]
protected theorem coe_zpow (a : { x : α // 0 ≤ x }) (n : ℤ) :
    ((a ^ n : { x : α // 0 ≤ x }) : α) = a ^ n :=
  rfl
#align nonneg.coe_zpow Nonneg.coe_zpow

/- warning: nonneg.mk_zpow -> Nonneg.mk_zpow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align nonneg.mk_zpow Nonneg.mk_zpowₓ'. -/
@[simp]
theorem mk_zpow (hx : 0 ≤ x) (n : ℤ) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, zpow_nonneg hx n⟩ :=
  rfl
#align nonneg.mk_zpow Nonneg.mk_zpow

/- warning: nonneg.linear_ordered_semifield -> Nonneg.linearOrderedSemifield is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α], LinearOrderedSemifield.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))))))) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α], LinearOrderedSemifield.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedSemiring.toPartialOrder.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))) x))
Case conversion may be inaccurate. Consider using '#align nonneg.linear_ordered_semifield Nonneg.linearOrderedSemifieldₓ'. -/
instance linearOrderedSemifield : LinearOrderedSemifield { x : α // 0 ≤ x } :=
  Subtype.coe_injective.LinearOrderedSemifield _ Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul Nonneg.coe_inv Nonneg.coe_div (fun _ _ => rfl) Nonneg.coe_pow Nonneg.coe_zpow
    Nonneg.coe_nat_cast (fun _ _ => rfl) fun _ _ => rfl
#align nonneg.linear_ordered_semifield Nonneg.linearOrderedSemifield

end LinearOrderedSemifield

/- warning: nonneg.canonically_linear_ordered_semifield -> Nonneg.canonicallyLinearOrderedSemifield is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α], CanonicallyLinearOrderedSemifield.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))))))) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α], CanonicallyLinearOrderedSemifield.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))))) x))
Case conversion may be inaccurate. Consider using '#align nonneg.canonically_linear_ordered_semifield Nonneg.canonicallyLinearOrderedSemifieldₓ'. -/
instance canonicallyLinearOrderedSemifield [LinearOrderedField α] :
    CanonicallyLinearOrderedSemifield { x : α // 0 ≤ x } :=
  { Nonneg.linearOrderedSemifield, Nonneg.canonicallyOrderedCommSemiring with }
#align nonneg.canonically_linear_ordered_semifield Nonneg.canonicallyLinearOrderedSemifield

/- warning: nonneg.linear_ordered_comm_group_with_zero -> Nonneg.linearOrderedCommGroupWithZero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α], LinearOrderedCommGroupWithZero.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))))))) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α], LinearOrderedCommGroupWithZero.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))))) x))
Case conversion may be inaccurate. Consider using '#align nonneg.linear_ordered_comm_group_with_zero Nonneg.linearOrderedCommGroupWithZeroₓ'. -/
instance linearOrderedCommGroupWithZero [LinearOrderedField α] :
    LinearOrderedCommGroupWithZero { x : α // 0 ≤ x } :=
  inferInstance
#align nonneg.linear_ordered_comm_group_with_zero Nonneg.linearOrderedCommGroupWithZero

end Nonneg

