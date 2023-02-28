/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.group.inj_surj
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Group.Defs
import Mathbin.Algebra.Order.Monoid.Basic
import Mathbin.Algebra.Order.Group.Instances

/-!
# Pull back ordered groups along injective maps.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α β : Type _}

/- warning: function.injective.ordered_comm_group -> Function.Injective.orderedCommGroup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Inv.{u2} β] [_inst_5 : Div.{u2} β] [_inst_6 : Pow.{u2, 0} β Nat] [_inst_7 : Pow.{u2, 0} β Int] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_2)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))) (f x) (f y))) -> (forall (x : β), Eq.{succ u1} α (f (Inv.inv.{u2} β _inst_4 x)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) (f x))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β _inst_5) x y)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_6) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) (f x) n)) -> (forall (x : β) (n : Int), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Int β (instHPow.{u2, 0} β Int _inst_7) x n)) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))) (f x) n)) -> (OrderedCommGroup.{u2} β)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Inv.{u2} β] [_inst_5 : Div.{u2} β] [_inst_6 : Pow.{u2, 0} β Nat] [_inst_7 : Pow.{u2, 0} β Int] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_2))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))) (f x) (f y))) -> (forall (x : β), Eq.{succ u1} α (f (Inv.inv.{u2} β _inst_4 x)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) (f x))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β _inst_5) x y)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_6) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) (f x) n)) -> (forall (x : β) (n : Int), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Int β (instHPow.{u2, 0} β Int _inst_7) x n)) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))) (f x) n)) -> (OrderedCommGroup.{u2} β)
Case conversion may be inaccurate. Consider using '#align function.injective.ordered_comm_group Function.Injective.orderedCommGroupₓ'. -/
/-- Pullback an `ordered_comm_group` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.orderedAddCommGroup
      "Pullback an `ordered_add_comm_group` under an injective map."]
def Function.Injective.orderedCommGroup [OrderedCommGroup α] {β : Type _} [One β] [Mul β] [Inv β]
    [Div β] [Pow β ℕ] [Pow β ℤ] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : OrderedCommGroup β :=
  { PartialOrder.lift f hf, hf.OrderedCommMonoid f one mul npow,
    hf.CommGroup f one mul inv div npow zpow with }
#align function.injective.ordered_comm_group Function.Injective.orderedCommGroup
#align function.injective.ordered_add_comm_group Function.Injective.orderedAddCommGroup

/- warning: function.injective.linear_ordered_comm_group -> Function.Injective.linearOrderedCommGroup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommGroup.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Inv.{u2} β] [_inst_5 : Div.{u2} β] [_inst_6 : Pow.{u2, 0} β Nat] [_inst_7 : Pow.{u2, 0} β Int] [_inst_8 : Sup.{u2} β] [_inst_9 : Inf.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_2)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1))))))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))))) (f x) (f y))) -> (forall (x : β), Eq.{succ u1} α (f (Inv.inv.{u2} β _inst_4 x)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1))))) (f x))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β _inst_5) x y)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_6) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1))))))) (f x) n)) -> (forall (x : β) (n : Int), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Int β (instHPow.{u2, 0} β Int _inst_7) x n)) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))) (f x) n)) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (Sup.sup.{u2} β _inst_8 x y)) (LinearOrder.max.{u1} α (LinearOrderedCommGroup.toLinearOrder.{u1} α _inst_1) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (Inf.inf.{u2} β _inst_9 x y)) (LinearOrder.min.{u1} α (LinearOrderedCommGroup.toLinearOrder.{u1} α _inst_1) (f x) (f y))) -> (LinearOrderedCommGroup.{u2} β)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommGroup.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Inv.{u2} β] [_inst_5 : Div.{u2} β] [_inst_6 : Pow.{u2, 0} β Nat] [_inst_7 : Pow.{u2, 0} β Int] [_inst_8 : Sup.{u2} β] [_inst_9 : Inf.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_2))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))))) (f x) (f y))) -> (forall (x : β), Eq.{succ u1} α (f (Inv.inv.{u2} β _inst_4 x)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1))))))) (f x))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β _inst_5) x y)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_6) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1))))))) (f x) n)) -> (forall (x : β) (n : Int), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Int β (instHPow.{u2, 0} β Int _inst_7) x n)) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))) (f x) n)) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (Sup.sup.{u2} β _inst_8 x y)) (Max.max.{u1} α (LinearOrderedCommGroup.toMax.{u1} α _inst_1) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (Inf.inf.{u2} β _inst_9 x y)) (Min.min.{u1} α (LinearOrderedCommGroup.toMin.{u1} α _inst_1) (f x) (f y))) -> (LinearOrderedCommGroup.{u2} β)
Case conversion may be inaccurate. Consider using '#align function.injective.linear_ordered_comm_group Function.Injective.linearOrderedCommGroupₓ'. -/
/-- Pullback a `linear_ordered_comm_group` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.linearOrderedAddCommGroup
      "Pullback a `linear_ordered_add_comm_group` under an injective map."]
def Function.Injective.linearOrderedCommGroup [LinearOrderedCommGroup α] {β : Type _} [One β]
    [Mul β] [Inv β] [Div β] [Pow β ℕ] [Pow β ℤ] [Sup β] [Inf β] (f : β → α)
    (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommGroup β :=
  { LinearOrder.lift f hf hsup hinf, hf.OrderedCommGroup f one mul inv div npow zpow with }
#align function.injective.linear_ordered_comm_group Function.Injective.linearOrderedCommGroup
#align function.injective.linear_ordered_add_comm_group Function.Injective.linearOrderedAddCommGroup

