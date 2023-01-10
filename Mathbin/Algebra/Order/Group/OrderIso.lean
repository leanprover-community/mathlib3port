/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.group.order_iso
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
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
  forall (α : Type.{u1}) [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.209 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.211 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.209 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.211) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.224 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.226 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.224 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.226)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.246 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.248 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.246 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.248)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.261 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.263 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.261 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.263)], OrderIso.{u1, u1} α (OrderDual.{u1} α) _inst_2 (OrderDual.instLEOrderDual.{u1} α _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso.inv OrderIso.invₓ'. -/
/-- `x ↦ x⁻¹` as an order-reversing equivalence. -/
@[to_additive "`x ↦ -x` as an order-reversing equivalence.", simps]
def OrderIso.inv : α ≃o αᵒᵈ
    where
  toEquiv := (Equiv.inv α).trans OrderDual.toDual
  map_rel_iff' a b := @inv_le_inv_iff α _ _ _ _ _ _
#align order_iso.inv OrderIso.inv

end

/- warning: inv_le' -> inv_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.324 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.326 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.324 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.326) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.339 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.341 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.339 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.341)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.361 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.363 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.361 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.363)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.376 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.378 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.376 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.378)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a)
Case conversion may be inaccurate. Consider using '#align inv_le' inv_le'ₓ'. -/
@[to_additive neg_le]
theorem inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
  (OrderIso.inv α).symm_apply_le
#align inv_le' inv_le'

alias inv_le' ↔ inv_le_of_inv_le' _

attribute [to_additive neg_le_of_neg_le] inv_le_of_inv_le'

/- warning: le_inv' -> le_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LE.le.{u1} α _inst_2 b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.437 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.439 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.437 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.439) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.452 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.454 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.452 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.454)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.474 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.476 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.474 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.476)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.489 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.491 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.489 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.491)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LE.le.{u1} α _inst_2 b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align le_inv' le_inv'ₓ'. -/
@[to_additive le_neg]
theorem le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
  (OrderIso.inv α).le_symm_apply
#align le_inv' le_inv'

end TypeclassesLeftRightLe

end Group

alias le_inv' ↔ le_inv_of_le_inv _

attribute [to_additive] le_inv_of_le_inv

section Group

variable [Group α] [LE α]

section Right

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}

/- warning: order_iso.mul_right -> OrderIso.mulRight is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)], α -> (OrderIso.{u1, u1} α α _inst_2 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.627 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.629 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.627 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.629)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.642 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.644 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.642 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.644)], α -> (OrderIso.{u1, u1} α α _inst_2 _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso.mul_right OrderIso.mulRightₓ'. -/
/-- `equiv.mul_right` as an `order_iso`. See also `order_embedding.mul_right`. -/
@[to_additive "`equiv.add_right` as an `order_iso`. See also `order_embedding.add_right`.",
  simps (config := { simpRhs := true }) toEquiv apply]
def OrderIso.mulRight (a : α) : α ≃o α
    where
  map_rel_iff' _ _ := mul_le_mul_iff_right a
  toEquiv := Equiv.mulRight a
#align order_iso.mul_right OrderIso.mulRight

/- warning: order_iso.mul_right_symm -> OrderIso.mulRight_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] (a : α), Eq.{succ u1} (OrderIso.{u1, u1} α α _inst_2 _inst_2) (OrderIso.symm.{u1, u1} α α _inst_2 _inst_2 (OrderIso.mulRight.{u1} α _inst_1 _inst_2 _inst_3 a)) (OrderIso.mulRight.{u1} α _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.722 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.724 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.722 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.724)) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.737 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.739 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.737 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.739)] (a : α), Eq.{succ u1} (OrderIso.{u1, u1} α α _inst_2 _inst_2) (OrderIso.symm.{u1, u1} α α _inst_2 _inst_2 (OrderIso.mulRight.{u1} α _inst_1 _inst_2 _inst_3 a)) (OrderIso.mulRight.{u1} α _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align order_iso.mul_right_symm OrderIso.mulRight_symmₓ'. -/
@[simp, to_additive]
theorem OrderIso.mulRight_symm (a : α) : (OrderIso.mulRight a).symm = OrderIso.mulRight a⁻¹ :=
  by
  ext x
  rfl
#align order_iso.mul_right_symm OrderIso.mulRight_symm

end Right

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

/- warning: order_iso.mul_left -> OrderIso.mulLeft is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)], α -> (OrderIso.{u1, u1} α α _inst_2 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.846 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.848 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.846 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.848) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.861 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.863 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.861 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.863)], α -> (OrderIso.{u1, u1} α α _inst_2 _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso.mul_left OrderIso.mulLeftₓ'. -/
/-- `equiv.mul_left` as an `order_iso`. See also `order_embedding.mul_left`. -/
@[to_additive "`equiv.add_left` as an `order_iso`. See also `order_embedding.add_left`.",
  simps (config := { simpRhs := true }) toEquiv apply]
def OrderIso.mulLeft (a : α) : α ≃o α
    where
  map_rel_iff' _ _ := mul_le_mul_iff_left a
  toEquiv := Equiv.mulLeft a
#align order_iso.mul_left OrderIso.mulLeft

/- warning: order_iso.mul_left_symm -> OrderIso.mulLeft_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] (a : α), Eq.{succ u1} (OrderIso.{u1, u1} α α _inst_2 _inst_2) (OrderIso.symm.{u1, u1} α α _inst_2 _inst_2 (OrderIso.mulLeft.{u1} α _inst_1 _inst_2 _inst_3 a)) (OrderIso.mulLeft.{u1} α _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.934 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.936 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.934 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.936) (fun (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.949 : α) (x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.951 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.949 x._@.Mathlib.Algebra.Order.Group.OrderIso._hyg.951)] (a : α), Eq.{succ u1} (OrderIso.{u1, u1} α α _inst_2 _inst_2) (OrderIso.symm.{u1, u1} α α _inst_2 _inst_2 (OrderIso.mulLeft.{u1} α _inst_1 _inst_2 _inst_3 a)) (OrderIso.mulLeft.{u1} α _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align order_iso.mul_left_symm OrderIso.mulLeft_symmₓ'. -/
@[simp, to_additive]
theorem OrderIso.mulLeft_symm (a : α) : (OrderIso.mulLeft a).symm = OrderIso.mulLeft a⁻¹ :=
  by
  ext x
  rfl
#align order_iso.mul_left_symm OrderIso.mulLeft_symm

end Left

end Group

