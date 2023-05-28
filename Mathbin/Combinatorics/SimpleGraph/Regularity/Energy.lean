/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.simple_graph.regularity.energy
! leanprover-community/mathlib commit bf7ef0e83e5b7e6c1169e97f055e58a2e4e9d52d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Algebra.Module.Basic
import Mathbin.Combinatorics.SimpleGraph.Density
import Mathbin.Data.Rat.BigOperators

/-!
# Energy of a partition

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the energy of a partition.

The energy is the auxiliary quantity that drives the induction process in the proof of Szemerédi's
Regularity Lemma. As long as we do not have a suitable equipartition, we will find a new one that
has an energy greater than the previous one plus some fixed constant.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/


open Finset

open BigOperators

variable {α : Type _} [DecidableEq α] {s : Finset α} (P : Finpartition s) (G : SimpleGraph α)
  [DecidableRel G.Adj]

namespace Finpartition

/- warning: finpartition.energy -> Finpartition.energy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, (Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s) -> (forall (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], Rat)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, (Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s) -> (forall (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], Rat)
Case conversion may be inaccurate. Consider using '#align finpartition.energy Finpartition.energyₓ'. -/
/-- The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity
lemma.  -/
def energy : ℚ :=
  (∑ uv in P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2) / P.parts.card ^ 2
#align finpartition.energy Finpartition.energy

/- warning: finpartition.energy_nonneg -> Finpartition.energy_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s) (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) (Finpartition.energy.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P G (fun (a : α) (b : α) => _inst_2 a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s) (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) (Finpartition.energy.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P G (fun (a : α) (b : α) => _inst_2 a b))
Case conversion may be inaccurate. Consider using '#align finpartition.energy_nonneg Finpartition.energy_nonnegₓ'. -/
theorem energy_nonneg : 0 ≤ P.energy G :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) <| sq_nonneg _
#align finpartition.energy_nonneg Finpartition.energy_nonneg

/- warning: finpartition.energy_le_one -> Finpartition.energy_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s) (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], LE.le.{0} Rat Rat.hasLe (Finpartition.energy.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P G (fun (a : α) (b : α) => _inst_2 a b)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s) (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], LE.le.{0} Rat Rat.instLERat (Finpartition.energy.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P G (fun (a : α) (b : α) => _inst_2 a b)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))
Case conversion may be inaccurate. Consider using '#align finpartition.energy_le_one Finpartition.energy_le_oneₓ'. -/
theorem energy_le_one : P.energy G ≤ 1 :=
  div_le_of_nonneg_of_le_mul (sq_nonneg _) zero_le_one <|
    calc
      (∑ uv in P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2) ≤ P.parts.offDiag.card • 1 :=
        sum_le_card_nsmul _ _ 1 fun uv _ =>
          (sq_le_one_iff <| G.edgeDensity_nonneg _ _).2 <| G.edgeDensity_le_one _ _
      _ = P.parts.offDiag.card := (Nat.smul_one_eq_coe _)
      _ ≤ _ := by rw [off_diag_card, one_mul, ← Nat.cast_pow, Nat.cast_le, sq]; exact tsub_le_self
      
#align finpartition.energy_le_one Finpartition.energy_le_one

/- warning: finpartition.coe_energy -> Finpartition.coe_energy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s) (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {𝕜 : Type.{u2}} [_inst_3 : LinearOrderedField.{u2} 𝕜], Eq.{succ u2} 𝕜 ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u2} Rat 𝕜 (CoeTCₓ.coe.{1, succ u2} Rat 𝕜 (Rat.castCoe.{u2} 𝕜 (DivisionRing.toHasRatCast.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_3)))))) (Finpartition.energy.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P G (fun (a : α) (b : α) => _inst_2 a b))) (HDiv.hDiv.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHDiv.{u2} 𝕜 (DivInvMonoid.toHasDiv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_3))))) (Finset.sum.{u2, u1} 𝕜 (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) (AddCommGroup.toAddCommMonoid.{u2} 𝕜 (OrderedAddCommGroup.toAddCommGroup.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_3)))))) (Finset.offDiag.{u1} (Finset.{u1} α) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P)) (fun (uv : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) => HPow.hPow.{u2, 0, u2} 𝕜 Nat 𝕜 (instHPow.{u2, 0} 𝕜 Nat (Monoid.Pow.{u2} 𝕜 (Ring.toMonoid.{u2} 𝕜 (StrictOrderedRing.toRing.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_3))))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u2} Rat 𝕜 (CoeTCₓ.coe.{1, succ u2} Rat 𝕜 (Rat.castCoe.{u2} 𝕜 (DivisionRing.toHasRatCast.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_3)))))) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_2 a b) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) uv) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) uv))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (HPow.hPow.{u2, 0, u2} 𝕜 Nat 𝕜 (instHPow.{u2, 0} 𝕜 Nat (Monoid.Pow.{u2} 𝕜 (Ring.toMonoid.{u2} 𝕜 (StrictOrderedRing.toRing.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_3))))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u2} Nat 𝕜 (CoeTCₓ.coe.{1, succ u2} Nat 𝕜 (Nat.castCoe.{u2} 𝕜 (AddMonoidWithOne.toNatCast.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (StrictOrderedRing.toRing.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_3))))))))))) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.orderBot.{u1} α) s P))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s) (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {𝕜 : Type.{u2}} [_inst_3 : LinearOrderedField.{u2} 𝕜], Eq.{succ u2} 𝕜 (Rat.cast.{u2} 𝕜 (LinearOrderedField.toRatCast.{u2} 𝕜 _inst_3) (Finpartition.energy.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s P G (fun (a : α) (b : α) => _inst_2 a b))) (HDiv.hDiv.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHDiv.{u2} 𝕜 (LinearOrderedField.toDiv.{u2} 𝕜 _inst_3)) (Rat.cast.{u2} 𝕜 (LinearOrderedField.toRatCast.{u2} 𝕜 _inst_3) (Finset.sum.{0, u1} Rat (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) Rat.addCommMonoid (Finset.offDiag.{u1} (Finset.{u1} α) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P)) (fun (uv : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) => HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_2 a b) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) uv) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) uv)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) (Rat.cast.{u2} 𝕜 (LinearOrderedField.toRatCast.{u2} 𝕜 _inst_3) (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) (Finset.card.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s P))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align finpartition.coe_energy Finpartition.coe_energyₓ'. -/
@[simp, norm_cast]
theorem coe_energy {𝕜 : Type _} [LinearOrderedField 𝕜] :
    (P.energy G : 𝕜) = (∑ uv in P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2) / P.parts.card ^ 2 :=
  by rw [energy]; norm_cast
#align finpartition.coe_energy Finpartition.coe_energy

end Finpartition

