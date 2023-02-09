/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module order.partition.equipartition
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Equitable
import Mathbin.Order.Partition.Finpartition

/-!
# Finite equipartitions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines finite equipartitions, the partitions whose parts all are the same size up to a
difference of `1`.

## Main declarations

* `finpartition.is_equipartition`: Predicate for a `finpartition` to be an equipartition.
-/


open Finset Fintype

namespace Finpartition

variable {α : Type _} [DecidableEq α] {s t : Finset α} (P : Finpartition s)

/- warning: finpartition.is_equipartition -> Finpartition.IsEquipartition is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, (Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s) -> Prop
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, (Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s) -> Prop
Case conversion may be inaccurate. Consider using '#align finpartition.is_equipartition Finpartition.IsEquipartitionₓ'. -/
/-- An equipartition is a partition whose parts are all the same size, up to a difference of `1`. -/
def IsEquipartition : Prop :=
  (P.parts : Set (Finset α)).EquitableOn card
#align finpartition.is_equipartition Finpartition.IsEquipartition

/- warning: finpartition.is_equipartition_iff_card_parts_eq_average -> Finpartition.isEquipartition_iff_card_parts_eq_average is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s), Iff (Finpartition.IsEquipartition.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P) (forall (a : Finset.{u1} α), (Membership.Mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.hasMem.{u1} (Finset.{u1} α)) a (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P)) -> (Or (Eq.{1} Nat (Finset.card.{u1} α a) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P)))) (Eq.{1} Nat (Finset.card.{u1} α a) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s), Iff (Finpartition.IsEquipartition.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P) (forall (a : Finset.{u1} α), (Membership.mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.instMembershipFinset.{u1} (Finset.{u1} α)) a (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P)) -> (Or (Eq.{1} Nat (Finset.card.{u1} α a) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P)))) (Eq.{1} Nat (Finset.card.{u1} α a) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))
Case conversion may be inaccurate. Consider using '#align finpartition.is_equipartition_iff_card_parts_eq_average Finpartition.isEquipartition_iff_card_parts_eq_averageₓ'. -/
theorem isEquipartition_iff_card_parts_eq_average :
    P.IsEquipartition ↔
      ∀ a : Finset α,
        a ∈ P.parts → a.card = s.card / P.parts.card ∨ a.card = s.card / P.parts.card + 1 :=
  by simp_rw [is_equipartition, Finset.equitableOn_iff, P.sum_card_parts]
#align finpartition.is_equipartition_iff_card_parts_eq_average Finpartition.isEquipartition_iff_card_parts_eq_average

variable {P}

theorem Set.Subsingleton.isEquipartition (h : (P.parts : Set (Finset α)).Subsingleton) :
    P.IsEquipartition :=
  h.EquitableOn _
#align set.subsingleton.is_equipartition Set.Subsingleton.isEquipartition

/- warning: finpartition.is_equipartition.card_parts_eq_average -> Finpartition.IsEquipartition.card_parts_eq_average is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s}, (Finpartition.IsEquipartition.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P) -> (Membership.Mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.hasMem.{u1} (Finset.{u1} α)) t (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P)) -> (Or (Eq.{1} Nat (Finset.card.{u1} α t) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P)))) (Eq.{1} Nat (Finset.card.{u1} α t) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {P : Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s}, (Finpartition.IsEquipartition.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P) -> (Membership.mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.instMembershipFinset.{u1} (Finset.{u1} α)) t (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P)) -> (Or (Eq.{1} Nat (Finset.card.{u1} α t) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P)))) (Eq.{1} Nat (Finset.card.{u1} α t) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align finpartition.is_equipartition.card_parts_eq_average Finpartition.IsEquipartition.card_parts_eq_averageₓ'. -/
theorem IsEquipartition.card_parts_eq_average (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    t.card = s.card / P.parts.card ∨ t.card = s.card / P.parts.card + 1 :=
  P.isEquipartition_iff_card_parts_eq_average.1 hP _ ht
#align finpartition.is_equipartition.card_parts_eq_average Finpartition.IsEquipartition.card_parts_eq_average

/- warning: finpartition.is_equipartition.average_le_card_part -> Finpartition.IsEquipartition.average_le_card_part is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s}, (Finpartition.IsEquipartition.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P) -> (Membership.Mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.hasMem.{u1} (Finset.{u1} α)) t (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P)) -> (LE.le.{0} Nat Nat.hasLe (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P))) (Finset.card.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {P : Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s}, (Finpartition.IsEquipartition.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P) -> (Membership.mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.instMembershipFinset.{u1} (Finset.{u1} α)) t (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P)) -> (LE.le.{0} Nat instLENat (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P))) (Finset.card.{u1} α t))
Case conversion may be inaccurate. Consider using '#align finpartition.is_equipartition.average_le_card_part Finpartition.IsEquipartition.average_le_card_partₓ'. -/
theorem IsEquipartition.average_le_card_part (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    s.card / P.parts.card ≤ t.card := by
  rw [← P.sum_card_parts]
  exact equitable_on.le hP ht
#align finpartition.is_equipartition.average_le_card_part Finpartition.IsEquipartition.average_le_card_part

/- warning: finpartition.is_equipartition.card_part_le_average_add_one -> Finpartition.IsEquipartition.card_part_le_average_add_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s}, (Finpartition.IsEquipartition.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P) -> (Membership.Mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.hasMem.{u1} (Finset.{u1} α)) t (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P)) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α t) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {P : Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s}, (Finpartition.IsEquipartition.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P) -> (Membership.mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.instMembershipFinset.{u1} (Finset.{u1} α)) t (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P)) -> (LE.le.{0} Nat instLENat (Finset.card.{u1} α t) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) (Finset.card.{u1} α s) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align finpartition.is_equipartition.card_part_le_average_add_one Finpartition.IsEquipartition.card_part_le_average_add_oneₓ'. -/
theorem IsEquipartition.card_part_le_average_add_one (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    t.card ≤ s.card / P.parts.card + 1 :=
  by
  rw [← P.sum_card_parts]
  exact equitable_on.le_add_one hP ht
#align finpartition.is_equipartition.card_part_le_average_add_one Finpartition.IsEquipartition.card_part_le_average_add_one

/-! ### Discrete and indiscrete finpartition -/


variable (s)

#print Finpartition.bot_isEquipartition /-
theorem bot_isEquipartition : (⊥ : Finpartition s).IsEquipartition :=
  Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨1, by simp⟩
#align finpartition.bot_is_equipartition Finpartition.bot_isEquipartition
-/

/- warning: finpartition.top_is_equipartition -> Finpartition.top_isEquipartition is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Finpartition.IsEquipartition.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s (Top.top.{u1} (Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s) (OrderTop.toHasTop.{u1} (Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s) (Finpartition.hasLe.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s) (Finpartition.orderTop.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s (Finset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s (Bot.bot.{u1} (Finset.{u1} α) (OrderBot.toHasBot.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Finset.{u1} α) (Lattice.toSemilatticeInf.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))))) (Finset.orderBot.{u1} α)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) [inst._@.Mathlib.Order.Partition.Equipartition._hyg.372 : Decidable (Eq.{succ u1} (Finset.{u1} α) s (Bot.bot.{u1} (Finset.{u1} α) (GeneralizedBooleanAlgebra.toBot.{u1} (Finset.{u1} α) (Finset.instGeneralizedBooleanAlgebraFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))))], Finpartition.IsEquipartition.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s (Top.top.{u1} (Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s) (OrderTop.toTop.{u1} (Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s) (Finpartition.instLEFinpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s) (Finpartition.instOrderTopFinpartitionInstLEFinpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s inst._@.Mathlib.Order.Partition.Equipartition._hyg.372)))
Case conversion may be inaccurate. Consider using '#align finpartition.top_is_equipartition Finpartition.top_isEquipartitionₓ'. -/
theorem top_isEquipartition : (⊤ : Finpartition s).IsEquipartition :=
  (parts_top_subsingleton _).IsEquipartition
#align finpartition.top_is_equipartition Finpartition.top_isEquipartition

#print Finpartition.indiscrete_isEquipartition /-
theorem indiscrete_isEquipartition {hs : s ≠ ∅} : (indiscrete hs).IsEquipartition :=
  by
  rw [is_equipartition, indiscrete_parts, coe_singleton]
  exact Set.equitableOn_singleton s _
#align finpartition.indiscrete_is_equipartition Finpartition.indiscrete_isEquipartition
-/

end Finpartition

