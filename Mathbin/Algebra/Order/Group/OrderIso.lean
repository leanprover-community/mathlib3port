/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.group.order_iso
! leanprover-community/mathlib commit 6632ca2081e55ff5cf228ca63011979a0efb495b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Group.Defs
import Mathbin.Algebra.Hom.Equiv.Units.Basic

/-!
# Inverse and multiplication as order isomorphisms in ordered groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


open Function

universe u

variable {α : Type u}

section Group

variable [Group α]

section TypeclassesLeftRightLe

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
  {a b c d : α}

section

variable (α)

/- warning: order_iso.inv -> OrderIso.inv is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)], OrderIso.{u1, u1} α (OrderDual.{u1} α) _inst_2 (OrderDual.hasLe.{u1} α _inst_2)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.210 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.212 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.210 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.212) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.225 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.227 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.225 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.227)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.247 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.249 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.247 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.249)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.262 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.264 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.262 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.264)], OrderIso.{u1, u1} α (OrderDual.{u1} α) _inst_2 (OrderDual.instLEOrderDual.{u1} α _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso.inv OrderIso.invₓ'. -/
/-- `x ↦ x⁻¹` as an order-reversing equivalence. -/
@[to_additive "`x ↦ -x` as an order-reversing equivalence.", simps]
def OrderIso.inv : α ≃o αᵒᵈ
    where
  toEquiv := (Equiv.inv α).trans OrderDual.toDual
  map_rel_iff' a b := @inv_le_inv_iff α _ _ _ _ _ _
#align order_iso.inv OrderIso.inv
#align order_iso.neg OrderIso.neg

end

/- warning: inv_le' -> inv_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.327 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.329 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.327 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.329) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.342 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.344 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.342 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.344)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.364 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.366 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.364 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.366)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.379 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.381 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.379 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.381)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a)
Case conversion may be inaccurate. Consider using '#align inv_le' inv_le'ₓ'. -/
@[to_additive neg_le]
theorem inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
  (OrderIso.inv α).symm_apply_le
#align inv_le' inv_le'
#align neg_le neg_le

/- warning: inv_le_of_inv_le' -> inv_le_of_inv_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) -> (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.327 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.329 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.327 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.329) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.342 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.344 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.342 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.344)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.364 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.366 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.364 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.366)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.379 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.381 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.379 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.381)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) -> (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a)
Case conversion may be inaccurate. Consider using '#align inv_le_of_inv_le' inv_le_of_inv_le'ₓ'. -/
alias inv_le' ↔ inv_le_of_inv_le' _
#align inv_le_of_inv_le' inv_le_of_inv_le'

attribute [to_additive neg_le_of_neg_le] inv_le_of_inv_le'

/- warning: le_inv' -> le_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LE.le.{u1} α _inst_2 b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.438 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.440 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.438 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.440) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.453 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.455 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.453 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.455)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.475 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.477 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.475 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.477)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.490 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.492 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.490 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.492)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LE.le.{u1} α _inst_2 b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align le_inv' le_inv'ₓ'. -/
@[to_additive le_neg]
theorem le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
  (OrderIso.inv α).le_symm_apply
#align le_inv' le_inv'
#align le_neg le_neg

/- warning: order_iso.div_left -> OrderIso.divLeft is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)], α -> (OrderIso.{u1, u1} α (OrderDual.{u1} α) _inst_2 (OrderDual.hasLe.{u1} α _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.549 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.551 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.549 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.551) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.564 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.566 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.564 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.566)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.586 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.588 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.586 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.588)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.601 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.603 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.601 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.603)], α -> (OrderIso.{u1, u1} α (OrderDual.{u1} α) _inst_2 (OrderDual.instLEOrderDual.{u1} α _inst_2))
Case conversion may be inaccurate. Consider using '#align order_iso.div_left OrderIso.divLeftₓ'. -/
/-- `x ↦ a / x` as an order-reversing equivalence. -/
@[to_additive "`x ↦ a - x` as an order-reversing equivalence.", simps]
def OrderIso.divLeft (a : α) : α ≃o αᵒᵈ
    where
  toEquiv := (Equiv.divLeft a).trans OrderDual.toDual
  map_rel_iff' x y := @div_le_div_iff_left α _ _ _ _ _ _ _
#align order_iso.div_left OrderIso.divLeft
#align order_iso.sub_left OrderIso.subLeft

end TypeclassesLeftRightLe

end Group

/- warning: le_inv_of_le_inv -> le_inv_of_le_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) -> (LE.le.{u1} α _inst_2 b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.438 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.440 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.438 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.440) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.453 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.455 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.453 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.455)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.475 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.477 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.475 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.477)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.490 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.492 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.490 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.492)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) -> (LE.le.{u1} α _inst_2 b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align le_inv_of_le_inv le_inv_of_le_invₓ'. -/
alias le_inv' ↔ le_inv_of_le_inv _
#align le_inv_of_le_inv le_inv_of_le_inv

attribute [to_additive] le_inv_of_le_inv

section Group

variable [Group α] [LE α]

section Right

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}

/- warning: order_iso.mul_right -> OrderIso.mulRight is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)], α -> (OrderIso.{u1, u1} α α _inst_2 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.747 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.749 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.747 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.749)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.762 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.764 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.762 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.764)], α -> (OrderIso.{u1, u1} α α _inst_2 _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso.mul_right OrderIso.mulRightₓ'. -/
/-- `equiv.mul_right` as an `order_iso`. See also `order_embedding.mul_right`. -/
@[to_additive "`equiv.add_right` as an `order_iso`. See also `order_embedding.add_right`.",
  simps (config := { simpRhs := true }) toEquiv apply]
def OrderIso.mulRight (a : α) : α ≃o α
    where
  map_rel_iff' _ _ := mul_le_mul_iff_right a
  toEquiv := Equiv.mulRight a
#align order_iso.mul_right OrderIso.mulRight
#align order_iso.add_right OrderIso.addRight

/- warning: order_iso.mul_right_symm -> OrderIso.mulRight_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] (a : α), Eq.{succ u1} (OrderIso.{u1, u1} α α _inst_2 _inst_2) (OrderIso.symm.{u1, u1} α α _inst_2 _inst_2 (OrderIso.mulRight.{u1} α _inst_1 _inst_2 _inst_3 a)) (OrderIso.mulRight.{u1} α _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.863 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.865 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.863 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.865)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.878 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.880 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.878 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.880)] (a : α), Eq.{succ u1} (OrderIso.{u1, u1} α α _inst_2 _inst_2) (OrderIso.symm.{u1, u1} α α _inst_2 _inst_2 (OrderIso.mulRight.{u1} α _inst_1 _inst_2 _inst_3 a)) (OrderIso.mulRight.{u1} α _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align order_iso.mul_right_symm OrderIso.mulRight_symmₓ'. -/
@[simp, to_additive]
theorem OrderIso.mulRight_symm (a : α) : (OrderIso.mulRight a).symm = OrderIso.mulRight a⁻¹ :=
  by
  ext x
  rfl
#align order_iso.mul_right_symm OrderIso.mulRight_symm
#align order_iso.add_right_symm OrderIso.addRight_symm

/- warning: order_iso.div_right -> OrderIso.divRight is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)], α -> (OrderIso.{u1, u1} α α _inst_2 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.943 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.945 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.943 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.945)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.958 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.960 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.958 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.960)], α -> (OrderIso.{u1, u1} α α _inst_2 _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso.div_right OrderIso.divRightₓ'. -/
/-- `x ↦ x / a` as an order isomorphism. -/
@[to_additive "`x ↦ x - a` as an order isomorphism.", simps]
def OrderIso.divRight (a : α) : α ≃o α
    where
  toEquiv := Equiv.divRight a
  map_rel_iff' x y := div_le_div_iff_right a
#align order_iso.div_right OrderIso.divRight
#align order_iso.sub_right OrderIso.subRight

end Right

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

/- warning: order_iso.mul_left -> OrderIso.mulLeft is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)], α -> (OrderIso.{u1, u1} α α _inst_2 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1064 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1066 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1064 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1066) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1079 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1081 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1079 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1081)], α -> (OrderIso.{u1, u1} α α _inst_2 _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso.mul_left OrderIso.mulLeftₓ'. -/
/-- `equiv.mul_left` as an `order_iso`. See also `order_embedding.mul_left`. -/
@[to_additive "`equiv.add_left` as an `order_iso`. See also `order_embedding.add_left`.",
  simps (config := { simpRhs := true }) toEquiv apply]
def OrderIso.mulLeft (a : α) : α ≃o α
    where
  map_rel_iff' _ _ := mul_le_mul_iff_left a
  toEquiv := Equiv.mulLeft a
#align order_iso.mul_left OrderIso.mulLeft
#align order_iso.add_left OrderIso.addLeft

/- warning: order_iso.mul_left_symm -> OrderIso.mulLeft_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] (a : α), Eq.{succ u1} (OrderIso.{u1, u1} α α _inst_2 _inst_2) (OrderIso.symm.{u1, u1} α α _inst_2 _inst_2 (OrderIso.mulLeft.{u1} α _inst_1 _inst_2 _inst_3 a)) (OrderIso.mulLeft.{u1} α _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1174 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1176 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1174 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1176) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1189 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1191 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1189 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.1191)] (a : α), Eq.{succ u1} (OrderIso.{u1, u1} α α _inst_2 _inst_2) (OrderIso.symm.{u1, u1} α α _inst_2 _inst_2 (OrderIso.mulLeft.{u1} α _inst_1 _inst_2 _inst_3 a)) (OrderIso.mulLeft.{u1} α _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align order_iso.mul_left_symm OrderIso.mulLeft_symmₓ'. -/
@[simp, to_additive]
theorem OrderIso.mulLeft_symm (a : α) : (OrderIso.mulLeft a).symm = OrderIso.mulLeft a⁻¹ :=
  by
  ext x
  rfl
#align order_iso.mul_left_symm OrderIso.mulLeft_symm
#align order_iso.add_left_symm OrderIso.addLeft_symm

end Left

end Group

