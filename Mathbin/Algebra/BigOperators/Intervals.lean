/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module algebra.big_operators.intervals
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Module.Basic
import Mathbin.Data.Nat.Interval
import Mathbin.Tactic.Linarith.Default

/-!
# Results about big operators over intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove results about big operators over intervals (mostly the `ℕ`-valued `Ico m n`).
-/


universe u v w

open BigOperators Nat

namespace Finset

section Generic

variable {α : Type u} {β : Type v} {γ : Type w} {s₂ s₁ s : Finset α} {a : α} {g f : α → β}

variable [CommMonoid β]

/- warning: finset.prod_Ico_add' -> Finset.prod_Ico_add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u2} β] [_inst_2 : OrderedCancelAddCommMonoid.{u1} α] [_inst_3 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2))] (f : α -> β) (a : α) (b : α) (c : α), Eq.{succ u2} β (Finset.prod.{u2, u1} β α _inst_1 (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)) _inst_4 a b) (fun (x : α) => f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) x c))) (Finset.prod.{u2, u1} β α _inst_1 (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)) _inst_4 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) b c)) (fun (x : α) => f x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u2} β] [_inst_2 : OrderedCancelAddCommMonoid.{u1} α] [_inst_3 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2))] (f : α -> β) (a : α) (b : α) (c : α), Eq.{succ u2} β (Finset.prod.{u2, u1} β α _inst_1 (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)) _inst_4 a b) (fun (x : α) => f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) x c))) (Finset.prod.{u2, u1} β α _inst_1 (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)) _inst_4 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) b c)) (fun (x : α) => f x))
Case conversion may be inaccurate. Consider using '#align finset.prod_Ico_add' Finset.prod_Ico_add'ₓ'. -/
@[to_additive]
theorem prod_Ico_add' [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → β) (a b c : α) : (∏ x in Ico a b, f (x + c)) = ∏ x in Ico (a + c) (b + c), f x :=
  by
  rw [← map_add_right_Ico, Prod_map]
  rfl
#align finset.prod_Ico_add' Finset.prod_Ico_add'
#align finset.sum_Ico_add' Finset.sum_Ico_add'

/- warning: finset.prod_Ico_add -> Finset.prod_Ico_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u2} β] [_inst_2 : OrderedCancelAddCommMonoid.{u1} α] [_inst_3 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2))] (f : α -> β) (a : α) (b : α) (c : α), Eq.{succ u2} β (Finset.prod.{u2, u1} β α _inst_1 (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)) _inst_4 a b) (fun (x : α) => f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) c x))) (Finset.prod.{u2, u1} β α _inst_1 (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)) _inst_4 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) b c)) (fun (x : α) => f x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u2} β] [_inst_2 : OrderedCancelAddCommMonoid.{u1} α] [_inst_3 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)))] [_inst_4 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2))] (f : α -> β) (a : α) (b : α) (c : α), Eq.{succ u2} β (Finset.prod.{u2, u1} β α _inst_1 (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)) _inst_4 a b) (fun (x : α) => f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) c x))) (Finset.prod.{u2, u1} β α _inst_1 (Finset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_2)) _inst_4 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_2))))))) b c)) (fun (x : α) => f x))
Case conversion may be inaccurate. Consider using '#align finset.prod_Ico_add Finset.prod_Ico_addₓ'. -/
@[to_additive]
theorem prod_Ico_add [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → β) (a b c : α) : (∏ x in Ico a b, f (c + x)) = ∏ x in Ico (a + c) (b + c), f x :=
  by
  convert prod_Ico_add' f a b c
  simp_rw [add_comm]
#align finset.prod_Ico_add Finset.prod_Ico_add
#align finset.sum_Ico_add Finset.sum_Ico_add

/- warning: finset.sum_Ico_succ_top -> Finset.sum_Ico_succ_top is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} [_inst_2 : AddCommMonoid.{u1} δ] {a : Nat} {b : Nat}, (LE.le.{0} Nat Nat.hasLe a b) -> (forall (f : Nat -> δ), Eq.{succ u1} δ (Finset.sum.{u1, 0} δ Nat _inst_2 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) b (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => f k)) (HAdd.hAdd.{u1, u1, u1} δ δ δ (instHAdd.{u1} δ (AddZeroClass.toHasAdd.{u1} δ (AddMonoid.toAddZeroClass.{u1} δ (AddCommMonoid.toAddMonoid.{u1} δ _inst_2)))) (Finset.sum.{u1, 0} δ Nat _inst_2 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a b) (fun (k : Nat) => f k)) (f b)))
but is expected to have type
  forall {δ : Type.{u1}} [_inst_2 : AddCommMonoid.{u1} δ] {a : Nat} {b : Nat}, (LE.le.{0} Nat instLENat a b) -> (forall (f : Nat -> δ), Eq.{succ u1} δ (Finset.sum.{u1, 0} δ Nat _inst_2 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) b (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => f k)) (HAdd.hAdd.{u1, u1, u1} δ δ δ (instHAdd.{u1} δ (AddZeroClass.toAdd.{u1} δ (AddMonoid.toAddZeroClass.{u1} δ (AddCommMonoid.toAddMonoid.{u1} δ _inst_2)))) (Finset.sum.{u1, 0} δ Nat _inst_2 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a b) (fun (k : Nat) => f k)) (f b)))
Case conversion may be inaccurate. Consider using '#align finset.sum_Ico_succ_top Finset.sum_Ico_succ_topₓ'. -/
theorem sum_Ico_succ_top {δ : Type _} [AddCommMonoid δ] {a b : ℕ} (hab : a ≤ b) (f : ℕ → δ) :
    (∑ k in Ico a (b + 1), f k) = (∑ k in Ico a b, f k) + f b := by
  rw [Nat.Ico_succ_right_eq_insert_Ico hab, sum_insert right_not_mem_Ico, add_comm]
#align finset.sum_Ico_succ_top Finset.sum_Ico_succ_top

/- warning: finset.prod_Ico_succ_top -> Finset.prod_Ico_succ_top is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : Nat} {b : Nat}, (LE.le.{0} Nat Nat.hasLe a b) -> (forall (f : Nat -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) b (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => f k)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a b) (fun (k : Nat) => f k)) (f b)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : Nat} {b : Nat}, (LE.le.{0} Nat instLENat a b) -> (forall (f : Nat -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) b (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => f k)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a b) (fun (k : Nat) => f k)) (f b)))
Case conversion may be inaccurate. Consider using '#align finset.prod_Ico_succ_top Finset.prod_Ico_succ_topₓ'. -/
@[to_additive]
theorem prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
    (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b :=
  @sum_Ico_succ_top (Additive β) _ _ _ hab _
#align finset.prod_Ico_succ_top Finset.prod_Ico_succ_top
#align finset.sum_Ico_succ_top Finset.sum_Ico_succ_top

/- warning: finset.sum_eq_sum_Ico_succ_bot -> Finset.sum_eq_sum_Ico_succ_bot is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} [_inst_2 : AddCommMonoid.{u1} δ] {a : Nat} {b : Nat}, (LT.lt.{0} Nat Nat.hasLt a b) -> (forall (f : Nat -> δ), Eq.{succ u1} δ (Finset.sum.{u1, 0} δ Nat _inst_2 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a b) (fun (k : Nat) => f k)) (HAdd.hAdd.{u1, u1, u1} δ δ δ (instHAdd.{u1} δ (AddZeroClass.toHasAdd.{u1} δ (AddMonoid.toAddZeroClass.{u1} δ (AddCommMonoid.toAddMonoid.{u1} δ _inst_2)))) (f a) (Finset.sum.{u1, 0} δ Nat _inst_2 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) b) (fun (k : Nat) => f k))))
but is expected to have type
  forall {δ : Type.{u1}} [_inst_2 : AddCommMonoid.{u1} δ] {a : Nat} {b : Nat}, (LT.lt.{0} Nat instLTNat a b) -> (forall (f : Nat -> δ), Eq.{succ u1} δ (Finset.sum.{u1, 0} δ Nat _inst_2 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a b) (fun (k : Nat) => f k)) (HAdd.hAdd.{u1, u1, u1} δ δ δ (instHAdd.{u1} δ (AddZeroClass.toAdd.{u1} δ (AddMonoid.toAddZeroClass.{u1} δ (AddCommMonoid.toAddMonoid.{u1} δ _inst_2)))) (f a) (Finset.sum.{u1, 0} δ Nat _inst_2 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) b) (fun (k : Nat) => f k))))
Case conversion may be inaccurate. Consider using '#align finset.sum_eq_sum_Ico_succ_bot Finset.sum_eq_sum_Ico_succ_botₓ'. -/
theorem sum_eq_sum_Ico_succ_bot {δ : Type _} [AddCommMonoid δ] {a b : ℕ} (hab : a < b) (f : ℕ → δ) :
    (∑ k in Ico a b, f k) = f a + ∑ k in Ico (a + 1) b, f k :=
  by
  have ha : a ∉ Ico (a + 1) b := by simp
  rw [← sum_insert ha, Nat.Ico_insert_succ_left hab]
#align finset.sum_eq_sum_Ico_succ_bot Finset.sum_eq_sum_Ico_succ_bot

/- warning: finset.prod_eq_prod_Ico_succ_bot -> Finset.prod_eq_prod_Ico_succ_bot is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : Nat} {b : Nat}, (LT.lt.{0} Nat Nat.hasLt a b) -> (forall (f : Nat -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a b) (fun (k : Nat) => f k)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) b) (fun (k : Nat) => f k))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : Nat} {b : Nat}, (LT.lt.{0} Nat instLTNat a b) -> (forall (f : Nat -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a b) (fun (k : Nat) => f k)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) b) (fun (k : Nat) => f k))))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_prod_Ico_succ_bot Finset.prod_eq_prod_Ico_succ_botₓ'. -/
@[to_additive]
theorem prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → β) :
    (∏ k in Ico a b, f k) = f a * ∏ k in Ico (a + 1) b, f k :=
  @sum_eq_sum_Ico_succ_bot (Additive β) _ _ _ hab _
#align finset.prod_eq_prod_Ico_succ_bot Finset.prod_eq_prod_Ico_succ_bot
#align finset.sum_eq_sum_Ico_succ_bot Finset.sum_eq_sum_Ico_succ_bot

/- warning: finset.prod_Ico_consecutive -> Finset.prod_Ico_consecutive is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) {m : Nat} {n : Nat} {k : Nat}, (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{0} Nat Nat.hasLe n k) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (i : Nat) => f i)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder n k) (fun (i : Nat) => f i))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m k) (fun (i : Nat) => f i)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) {m : Nat} {n : Nat} {k : Nat}, (LE.le.{0} Nat instLENat m n) -> (LE.le.{0} Nat instLENat n k) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (i : Nat) => f i)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring n k) (fun (i : Nat) => f i))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m k) (fun (i : Nat) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_Ico_consecutive Finset.prod_Ico_consecutiveₓ'. -/
@[to_additive]
theorem prod_Ico_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i in Ico m n, f i) * ∏ i in Ico n k, f i) = ∏ i in Ico m k, f i :=
  Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm <| prod_union <| Ico_disjoint_Ico_consecutive m n k
#align finset.prod_Ico_consecutive Finset.prod_Ico_consecutive
#align finset.sum_Ico_consecutive Finset.sum_Ico_consecutive

/- warning: finset.prod_Ioc_consecutive -> Finset.prod_Ioc_consecutive is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) {m : Nat} {n : Nat} {k : Nat}, (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{0} Nat Nat.hasLe n k) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (i : Nat) => f i)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder n k) (fun (i : Nat) => f i))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m k) (fun (i : Nat) => f i)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) {m : Nat} {n : Nat} {k : Nat}, (LE.le.{0} Nat instLENat m n) -> (LE.le.{0} Nat instLENat n k) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (i : Nat) => f i)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring n k) (fun (i : Nat) => f i))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m k) (fun (i : Nat) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_Ioc_consecutive Finset.prod_Ioc_consecutiveₓ'. -/
@[to_additive]
theorem prod_Ioc_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i in Ioc m n, f i) * ∏ i in Ioc n k, f i) = ∏ i in Ioc m k, f i :=
  by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk, prod_union]
  apply disjoint_left.2 fun x hx h'x => _
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)
#align finset.prod_Ioc_consecutive Finset.prod_Ioc_consecutive
#align finset.sum_Ioc_consecutive Finset.sum_Ioc_consecutive

/- warning: finset.prod_Ioc_succ_top -> Finset.prod_Ioc_succ_top is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : Nat} {b : Nat}, (LE.le.{0} Nat Nat.hasLe a b) -> (forall (f : Nat -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) b (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => f k)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a b) (fun (k : Nat) => f k)) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) b (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : Nat} {b : Nat}, (LE.le.{0} Nat instLENat a b) -> (forall (f : Nat -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) b (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => f k)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a b) (fun (k : Nat) => f k)) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) b (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_Ioc_succ_top Finset.prod_Ioc_succ_topₓ'. -/
@[to_additive]
theorem prod_Ioc_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
    (∏ k in Ioc a (b + 1), f k) = (∏ k in Ioc a b, f k) * f (b + 1) := by
  rw [← prod_Ioc_consecutive _ hab (Nat.le_succ b), Nat.Ioc_succ_singleton, prod_singleton]
#align finset.prod_Ioc_succ_top Finset.prod_Ioc_succ_top
#align finset.sum_Ioc_succ_top Finset.sum_Ioc_succ_top

/- warning: finset.prod_range_mul_prod_Ico -> Finset.prod_range_mul_prod_Ico is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) {m : Nat} {n : Nat}, (LE.le.{0} Nat Nat.hasLe m n) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range m) (fun (k : Nat) => f k)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (k : Nat) => f k))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (k : Nat) => f k)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) {m : Nat} {n : Nat}, (LE.le.{0} Nat instLENat m n) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range m) (fun (k : Nat) => f k)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (k : Nat) => f k))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (k : Nat) => f k)))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_mul_prod_Ico Finset.prod_range_mul_prod_Icoₓ'. -/
@[to_additive]
theorem prod_range_mul_prod_Ico (f : ℕ → β) {m n : ℕ} (h : m ≤ n) :
    ((∏ k in range m, f k) * ∏ k in Ico m n, f k) = ∏ k in range n, f k :=
  Nat.Ico_zero_eq_range ▸ Nat.Ico_zero_eq_range ▸ prod_Ico_consecutive f m.zero_le h
#align finset.prod_range_mul_prod_Ico Finset.prod_range_mul_prod_Ico
#align finset.sum_range_add_sum_Ico Finset.sum_range_add_sum_Ico

/- warning: finset.prod_Ico_eq_mul_inv -> Finset.prod_Ico_eq_mul_inv is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} [_inst_2 : CommGroup.{u1} δ] (f : Nat -> δ) {m : Nat} {n : Nat}, (LE.le.{0} Nat Nat.hasLe m n) -> (Eq.{succ u1} δ (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (k : Nat) => f k)) (HMul.hMul.{u1, u1, u1} δ δ δ (instHMul.{u1} δ (MulOneClass.toHasMul.{u1} δ (Monoid.toMulOneClass.{u1} δ (DivInvMonoid.toMonoid.{u1} δ (Group.toDivInvMonoid.{u1} δ (CommGroup.toGroup.{u1} δ _inst_2)))))) (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.range n) (fun (k : Nat) => f k)) (Inv.inv.{u1} δ (DivInvMonoid.toHasInv.{u1} δ (Group.toDivInvMonoid.{u1} δ (CommGroup.toGroup.{u1} δ _inst_2))) (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.range m) (fun (k : Nat) => f k)))))
but is expected to have type
  forall {δ : Type.{u1}} [_inst_2 : CommGroup.{u1} δ] (f : Nat -> δ) {m : Nat} {n : Nat}, (LE.le.{0} Nat instLENat m n) -> (Eq.{succ u1} δ (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (k : Nat) => f k)) (HMul.hMul.{u1, u1, u1} δ δ δ (instHMul.{u1} δ (MulOneClass.toMul.{u1} δ (Monoid.toMulOneClass.{u1} δ (DivInvMonoid.toMonoid.{u1} δ (Group.toDivInvMonoid.{u1} δ (CommGroup.toGroup.{u1} δ _inst_2)))))) (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.range n) (fun (k : Nat) => f k)) (Inv.inv.{u1} δ (InvOneClass.toInv.{u1} δ (DivInvOneMonoid.toInvOneClass.{u1} δ (DivisionMonoid.toDivInvOneMonoid.{u1} δ (DivisionCommMonoid.toDivisionMonoid.{u1} δ (CommGroup.toDivisionCommMonoid.{u1} δ _inst_2))))) (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.range m) (fun (k : Nat) => f k)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_Ico_eq_mul_inv Finset.prod_Ico_eq_mul_invₓ'. -/
@[to_additive]
theorem prod_Ico_eq_mul_inv {δ : Type _} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    (∏ k in Ico m n, f k) = (∏ k in range n, f k) * (∏ k in range m, f k)⁻¹ :=
  eq_mul_inv_iff_mul_eq.2 <| by rw [mul_comm] <;> exact prod_range_mul_prod_Ico f h
#align finset.prod_Ico_eq_mul_inv Finset.prod_Ico_eq_mul_inv
#align finset.sum_Ico_eq_add_neg Finset.sum_Ico_eq_add_neg

/- warning: finset.prod_Ico_eq_div -> Finset.prod_Ico_eq_div is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} [_inst_2 : CommGroup.{u1} δ] (f : Nat -> δ) {m : Nat} {n : Nat}, (LE.le.{0} Nat Nat.hasLe m n) -> (Eq.{succ u1} δ (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (k : Nat) => f k)) (HDiv.hDiv.{u1, u1, u1} δ δ δ (instHDiv.{u1} δ (DivInvMonoid.toHasDiv.{u1} δ (Group.toDivInvMonoid.{u1} δ (CommGroup.toGroup.{u1} δ _inst_2)))) (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.range n) (fun (k : Nat) => f k)) (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.range m) (fun (k : Nat) => f k))))
but is expected to have type
  forall {δ : Type.{u1}} [_inst_2 : CommGroup.{u1} δ] (f : Nat -> δ) {m : Nat} {n : Nat}, (LE.le.{0} Nat instLENat m n) -> (Eq.{succ u1} δ (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (k : Nat) => f k)) (HDiv.hDiv.{u1, u1, u1} δ δ δ (instHDiv.{u1} δ (DivInvMonoid.toDiv.{u1} δ (Group.toDivInvMonoid.{u1} δ (CommGroup.toGroup.{u1} δ _inst_2)))) (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.range n) (fun (k : Nat) => f k)) (Finset.prod.{u1, 0} δ Nat (CommGroup.toCommMonoid.{u1} δ _inst_2) (Finset.range m) (fun (k : Nat) => f k))))
Case conversion may be inaccurate. Consider using '#align finset.prod_Ico_eq_div Finset.prod_Ico_eq_divₓ'. -/
@[to_additive]
theorem prod_Ico_eq_div {δ : Type _} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    (∏ k in Ico m n, f k) = (∏ k in range n, f k) / ∏ k in range m, f k := by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h
#align finset.prod_Ico_eq_div Finset.prod_Ico_eq_div
#align finset.sum_Ico_eq_sub Finset.sum_Ico_eq_sub

/- warning: finset.prod_range_sub_prod_range -> Finset.prod_range_sub_prod_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : CommGroup.{u1} α] {f : Nat -> α} {n : Nat} {m : Nat}, (LE.le.{0} Nat Nat.hasLe n m) -> (Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.range m) (fun (k : Nat) => f k)) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.range n) (fun (k : Nat) => f k))) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.filter.{0} Nat (fun (k : Nat) => LE.le.{0} Nat Nat.hasLe n k) (fun (a : Nat) => Nat.decidableLe n a) (Finset.range m)) (fun (k : Nat) => f k)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : CommGroup.{u1} α] {f : Nat -> α} {n : Nat} {m : Nat}, (LE.le.{0} Nat instLENat n m) -> (Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.range m) (fun (k : Nat) => f k)) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.range n) (fun (k : Nat) => f k))) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.filter.{0} Nat (fun (k : Nat) => LE.le.{0} Nat instLENat n k) (fun (a : Nat) => Nat.decLe n a) (Finset.range m)) (fun (k : Nat) => f k)))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_sub_prod_range Finset.prod_range_sub_prod_rangeₓ'. -/
@[to_additive]
theorem prod_range_sub_prod_range {α : Type _} [CommGroup α] {f : ℕ → α} {n m : ℕ} (hnm : n ≤ m) :
    ((∏ k in range m, f k) / ∏ k in range n, f k) = ∏ k in (range m).filterₓ fun k => n ≤ k, f k :=
  by
  rw [← prod_Ico_eq_div f hnm]
  congr
  apply Finset.ext
  simp only [mem_Ico, mem_filter, mem_range, *]
  tauto
#align finset.prod_range_sub_prod_range Finset.prod_range_sub_prod_range
#align finset.sum_range_sub_sum_range Finset.sum_range_sub_sum_range

#print Finset.sum_Ico_Ico_comm /-
/-- The two ways of summing over `(i,j)` in the range `a<=i<=j<b` are equal. -/
theorem sum_Ico_Ico_comm {M : Type _} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i in Finset.Ico a b, ∑ j in Finset.Ico i b, f i j) =
      ∑ j in Finset.Ico a b, ∑ i in Finset.Ico a (j + 1), f i j :=
  by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine'
            Finset.sum_bij' (fun (x : Σi : ℕ, ℕ) _ => (⟨x.2, x.1⟩ : Σi : ℕ, ℕ)) _ (fun _ _ => rfl)
              (fun (x : Σi : ℕ, ℕ) _ => (⟨x.2, x.1⟩ : Σi : ℕ, ℕ)) _ (by rintro ⟨⟩ _ <;> rfl)
              (by rintro ⟨⟩ _ <;> rfl) <;>
          simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
        rintro a b ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
      refine' ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;>
    linarith
#align finset.sum_Ico_Ico_comm Finset.sum_Ico_Ico_comm
-/

#print Finset.prod_Ico_eq_prod_range /-
@[to_additive]
theorem prod_Ico_eq_prod_range (f : ℕ → β) (m n : ℕ) :
    (∏ k in Ico m n, f k) = ∏ k in range (n - m), f (m + k) :=
  by
  by_cases h : m ≤ n
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h : n ≤ m := le_of_not_ge h
    rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty]
#align finset.prod_Ico_eq_prod_range Finset.prod_Ico_eq_prod_range
#align finset.sum_Ico_eq_sum_range Finset.sum_Ico_eq_sum_range
-/

#print Finset.prod_Ico_reflect /-
theorem prod_Ico_reflect (f : ℕ → β) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
    (∏ j in Ico k m, f (n - j)) = ∏ j in Ico (n + 1 - m) (n + 1 - k), f j :=
  by
  have : ∀ i < m, i ≤ n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  cases' lt_or_le k m with hkm hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine' (prod_image _).symm
    simp only [mem_Ico]
    rintro i ⟨ki, im⟩ j ⟨kj, jm⟩ Hij
    rw [← tsub_tsub_cancel_of_le (this _ im), Hij, tsub_tsub_cancel_of_le (this _ jm)]
  · simp [Ico_eq_empty_of_le, tsub_le_tsub_left, hkm]
#align finset.prod_Ico_reflect Finset.prod_Ico_reflect
-/

#print Finset.sum_Ico_reflect /-
theorem sum_Ico_reflect {δ : Type _} [AddCommMonoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
    (h : m ≤ n + 1) : (∑ j in Ico k m, f (n - j)) = ∑ j in Ico (n + 1 - m) (n + 1 - k), f j :=
  @prod_Ico_reflect (Multiplicative δ) _ f k m n h
#align finset.sum_Ico_reflect Finset.sum_Ico_reflect
-/

#print Finset.prod_range_reflect /-
theorem prod_range_reflect (f : ℕ → β) (n : ℕ) :
    (∏ j in range n, f (n - 1 - j)) = ∏ j in range n, f j :=
  by
  cases n
  · simp
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [prod_Ico_reflect _ _ le_rfl]
    simp
#align finset.prod_range_reflect Finset.prod_range_reflect
-/

#print Finset.sum_range_reflect /-
theorem sum_range_reflect {δ : Type _} [AddCommMonoid δ] (f : ℕ → δ) (n : ℕ) :
    (∑ j in range n, f (n - 1 - j)) = ∑ j in range n, f j :=
  @prod_range_reflect (Multiplicative δ) _ f n
#align finset.sum_range_reflect Finset.sum_range_reflect
-/

#print Finset.prod_Ico_id_eq_factorial /-
@[simp]
theorem prod_Ico_id_eq_factorial : ∀ n : ℕ, (∏ x in Ico 1 (n + 1), x) = n !
  | 0 => rfl
  | n + 1 => by
    rw [prod_Ico_succ_top <| Nat.succ_le_succ <| zero_le n, Nat.factorial_succ,
      prod_Ico_id_eq_factorial n, Nat.succ_eq_add_one, mul_comm]
#align finset.prod_Ico_id_eq_factorial Finset.prod_Ico_id_eq_factorial
-/

#print Finset.prod_range_add_one_eq_factorial /-
@[simp]
theorem prod_range_add_one_eq_factorial : ∀ n : ℕ, (∏ x in range n, x + 1) = n !
  | 0 => rfl
  | n + 1 => by simp [Finset.range_succ, prod_range_add_one_eq_factorial n]
#align finset.prod_range_add_one_eq_factorial Finset.prod_range_add_one_eq_factorial
-/

section GaussSum

#print Finset.sum_range_id_mul_two /-
/-- Gauss' summation formula -/
theorem sum_range_id_mul_two (n : ℕ) : (∑ i in range n, i) * 2 = n * (n - 1) :=
  calc
    (∑ i in range n, i) * 2 = (∑ i in range n, i) + ∑ i in range n, n - 1 - i := by
      rw [sum_range_reflect (fun i => i) n, mul_two]
    _ = ∑ i in range n, i + (n - 1 - i) := sum_add_distrib.symm
    _ = ∑ i in range n, n - 1 :=
      sum_congr rfl fun i hi => add_tsub_cancel_of_le <| Nat.le_pred_of_lt <| mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]
    
#align finset.sum_range_id_mul_two Finset.sum_range_id_mul_two
-/

#print Finset.sum_range_id /-
/-- Gauss' summation formula -/
theorem sum_range_id (n : ℕ) : (∑ i in range n, i) = n * (n - 1) / 2 := by
  rw [← sum_range_id_mul_two n, Nat.mul_div_cancel] <;> exact by decide
#align finset.sum_range_id Finset.sum_range_id
-/

end GaussSum

end Generic

section Nat

variable {β : Type _}

variable (f g : ℕ → β) {m n : ℕ}

section Group

variable [CommGroup β]

/- warning: finset.prod_range_succ_div_prod -> Finset.prod_range_succ_div_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} (f : Nat -> β) {n : Nat} [_inst_1 : CommGroup.{u1} β], Eq.{succ u1} β (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toHasDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => f i)) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.range n) (fun (i : Nat) => f i))) (f n)
but is expected to have type
  forall {β : Type.{u1}} (f : Nat -> β) {n : Nat} [_inst_1 : CommGroup.{u1} β], Eq.{succ u1} β (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => f i)) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.range n) (fun (i : Nat) => f i))) (f n)
Case conversion may be inaccurate. Consider using '#align finset.prod_range_succ_div_prod Finset.prod_range_succ_div_prodₓ'. -/
@[to_additive]
theorem prod_range_succ_div_prod : ((∏ i in range (n + 1), f i) / ∏ i in range n, f i) = f n :=
  div_eq_iff_eq_mul'.mpr <| prod_range_succ f n
#align finset.prod_range_succ_div_prod Finset.prod_range_succ_div_prod
#align finset.sum_range_succ_sub_sum Finset.sum_range_succ_sub_sum

/- warning: finset.prod_range_succ_div_top -> Finset.prod_range_succ_div_top is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} (f : Nat -> β) {n : Nat} [_inst_1 : CommGroup.{u1} β], Eq.{succ u1} β (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toHasDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => f i)) (f n)) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.range n) (fun (i : Nat) => f i))
but is expected to have type
  forall {β : Type.{u1}} (f : Nat -> β) {n : Nat} [_inst_1 : CommGroup.{u1} β], Eq.{succ u1} β (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => f i)) (f n)) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.range n) (fun (i : Nat) => f i))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_succ_div_top Finset.prod_range_succ_div_topₓ'. -/
@[to_additive]
theorem prod_range_succ_div_top : (∏ i in range (n + 1), f i) / f n = ∏ i in range n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_range_succ f n
#align finset.prod_range_succ_div_top Finset.prod_range_succ_div_top
#align finset.sum_range_succ_sub_top Finset.sum_range_succ_sub_top

/- warning: finset.prod_Ico_div_bot -> Finset.prod_Ico_div_bot is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} (f : Nat -> β) {m : Nat} {n : Nat} [_inst_1 : CommGroup.{u1} β], (LT.lt.{0} Nat Nat.hasLt m n) -> (Eq.{succ u1} β (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toHasDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (i : Nat) => f i)) (f m)) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) n) (fun (i : Nat) => f i)))
but is expected to have type
  forall {β : Type.{u1}} (f : Nat -> β) {m : Nat} {n : Nat} [_inst_1 : CommGroup.{u1} β], (LT.lt.{0} Nat instLTNat m n) -> (Eq.{succ u1} β (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (i : Nat) => f i)) (f m)) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) n) (fun (i : Nat) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_Ico_div_bot Finset.prod_Ico_div_botₓ'. -/
@[to_additive]
theorem prod_Ico_div_bot (hmn : m < n) : (∏ i in Ico m n, f i) / f m = ∏ i in Ico (m + 1) n, f i :=
  div_eq_iff_eq_mul'.mpr <| prod_eq_prod_Ico_succ_bot hmn _
#align finset.prod_Ico_div_bot Finset.prod_Ico_div_bot
#align finset.sum_Ico_sub_bot Finset.sum_Ico_sub_bot

/- warning: finset.prod_Ico_succ_div_top -> Finset.prod_Ico_succ_div_top is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} (f : Nat -> β) {m : Nat} {n : Nat} [_inst_1 : CommGroup.{u1} β], (LE.le.{0} Nat Nat.hasLe m n) -> (Eq.{succ u1} β (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toHasDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => f i)) (f n)) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (i : Nat) => f i)))
but is expected to have type
  forall {β : Type.{u1}} (f : Nat -> β) {m : Nat} {n : Nat} [_inst_1 : CommGroup.{u1} β], (LE.le.{0} Nat instLENat m n) -> (Eq.{succ u1} β (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => f i)) (f n)) (Finset.prod.{u1, 0} β Nat (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (i : Nat) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_Ico_succ_div_top Finset.prod_Ico_succ_div_topₓ'. -/
@[to_additive]
theorem prod_Ico_succ_div_top (hmn : m ≤ n) :
    (∏ i in Ico m (n + 1), f i) / f n = ∏ i in Ico m n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_Ico_succ_top hmn _
#align finset.prod_Ico_succ_div_top Finset.prod_Ico_succ_div_top
#align finset.sum_Ico_succ_sub_top Finset.sum_Ico_succ_sub_top

end Group

end Nat

section Module

variable {R M : Type _} [Ring R] [AddCommGroup M] [Module R M] (f : ℕ → R) (g : ℕ → M) {m n : ℕ}

open Finset

-- mathport name: «exprG »
-- The partial sum of `g`, starting from zero
local notation "G " n:80 => ∑ i in range n, g i

/- warning: finset.sum_Ico_by_parts -> Finset.sum_Ico_by_parts is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (f : Nat -> R) (g : Nat -> M) {m : Nat} {n : Nat}, (LT.lt.{0} Nat Nat.hasLt m n) -> (Eq.{succ u2} M (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (i : Nat) => SMul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (f i) (g i))) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toHasSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toHasSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) (SMul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (f (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range n) (fun (i : Nat) => g i))) (SMul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (f m) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range m) (fun (i : Nat) => g i)))) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => SMul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (f i)) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => g i))))))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (f : Nat -> R) (g : Nat -> M) {m : Nat} {n : Nat}, (LT.lt.{0} Nat instLTNat m n) -> (Eq.{succ u2} M (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (i : Nat) => HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))) (f i) (g i))) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) (HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))) (f (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range n) (fun (i : Nat) => g i))) (HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))) (f m) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range m) (fun (i : Nat) => g i)))) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R _inst_1)) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (f i)) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => g i))))))
Case conversion may be inaccurate. Consider using '#align finset.sum_Ico_by_parts Finset.sum_Ico_by_partsₓ'. -/
/-- **Summation by parts**, also known as **Abel's lemma** or an **Abel transformation** -/
theorem sum_Ico_by_parts (hmn : m < n) :
    (∑ i in Ico m n, f i • g i) =
      f (n - 1) • G n - f m • G m - ∑ i in Ico m (n - 1), (f (i + 1) - f i) • G (i + 1) :=
  by
  have h₁ : (∑ i in Ico (m + 1) n, f i • G i) = ∑ i in Ico m (n - 1), f (i + 1) • G (i + 1) :=
    by
    conv in n => rw [← Nat.sub_add_cancel (Nat.one_le_of_lt hmn)]
    rw [← sum_Ico_add']
  have h₂ :
    (∑ i in Ico (m + 1) n, f i • G (i + 1)) =
      (∑ i in Ico m (n - 1), f i • G (i + 1)) + f (n - 1) • G n - f m • G (m + 1) :=
    by
    rw [← sum_Ico_sub_bot _ hmn, ← sum_Ico_succ_sub_top _ (Nat.le_pred_of_lt hmn),
      Nat.sub_add_cancel (pos_of_gt hmn), sub_add_cancel]
  rw [sum_eq_sum_Ico_succ_bot hmn]
  conv => pattern (occs := 2) f _ • g _ <;> (rw [← sum_range_succ_sub_sum g])
  simp_rw [smul_sub, sum_sub_distrib, h₂, h₁]
  conv_lhs =>
    congr
    skip
    rw [← add_sub, add_comm, ← add_sub, ← sum_sub_distrib]
  have : ∀ i, f i • G (i + 1) - f (i + 1) • G (i + 1) = -((f (i + 1) - f i) • G (i + 1)) :=
    by
    intro i
    rw [sub_smul]
    abel
  simp_rw [this, sum_neg_distrib, sum_range_succ, smul_add]
  abel
#align finset.sum_Ico_by_parts Finset.sum_Ico_by_parts

variable (n)

/- warning: finset.sum_range_by_parts -> Finset.sum_range_by_parts is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (f : Nat -> R) (g : Nat -> M) (n : Nat), Eq.{succ u2} M (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range n) (fun (i : Nat) => SMul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (f i) (g i))) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toHasSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) (SMul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (f (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range n) (fun (i : Nat) => g i))) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => SMul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (f i)) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => g i)))))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (f : Nat -> R) (g : Nat -> M) (n : Nat), Eq.{succ u2} M (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range n) (fun (i : Nat) => HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))) (f i) (g i))) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) (HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))) (f (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range n) (fun (i : Nat) => g i))) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => HSMul.hSMul.{u1, u2, u2} R M M (instHSMul.{u1, u2} R M (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R _inst_1)) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (f i)) (Finset.sum.{u2, 0} M Nat (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => g i)))))
Case conversion may be inaccurate. Consider using '#align finset.sum_range_by_parts Finset.sum_range_by_partsₓ'. -/
/-- **Summation by parts** for ranges -/
theorem sum_range_by_parts :
    (∑ i in range n, f i • g i) =
      f (n - 1) • G n - ∑ i in range (n - 1), (f (i + 1) - f i) • G (i + 1) :=
  by
  by_cases hn : n = 0
  · simp [hn]
  ·
    rw [range_eq_Ico, sum_Ico_by_parts f g (Nat.pos_of_ne_zero hn), sum_range_zero, smul_zero,
      sub_zero, range_eq_Ico]
#align finset.sum_range_by_parts Finset.sum_range_by_parts

end Module

end Finset

