/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module data.int.conditionally_complete_order
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Data.Int.LeastGreatest

/-!
## `ℤ` forms a conditionally complete linear order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The integers form a conditionally complete linear order.
-/


open Int

open Classical

noncomputable section

instance : ConditionallyCompleteLinearOrder ℤ :=
  { Int.linearOrder,
    LinearOrder.toLattice with
    supₛ := fun s =>
      if h : s.Nonempty ∧ BddAbove s then
        greatestOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
      else 0
    infₛ := fun s =>
      if h : s.Nonempty ∧ BddBelow s then
        leastOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
      else 0
    le_cSup := by
      intro s n hs hns
      have : s.nonempty ∧ BddAbove s := ⟨⟨n, hns⟩, hs⟩
      rw [dif_pos this]
      exact (greatest_of_bdd _ _ _).2.2 n hns
    cSup_le := by
      intro s n hs hns
      have : s.nonempty ∧ BddAbove s := ⟨hs, ⟨n, hns⟩⟩
      rw [dif_pos this]
      exact hns (greatest_of_bdd _ (Classical.choose_spec this.2) _).2.1
    cInf_le := by
      intro s n hs hns
      have : s.nonempty ∧ BddBelow s := ⟨⟨n, hns⟩, hs⟩
      rw [dif_pos this]
      exact (least_of_bdd _ _ _).2.2 n hns
    le_cInf := by
      intro s n hs hns
      have : s.nonempty ∧ BddBelow s := ⟨hs, ⟨n, hns⟩⟩
      rw [dif_pos this]
      exact hns (least_of_bdd _ (Classical.choose_spec this.2) _).2.1 }

namespace Int

/- warning: int.cSup_eq_greatest_of_bdd -> Int.csupₛ_eq_greatest_of_bdd is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Int} [_inst_1 : DecidablePred.{1} Int (fun (_x : Int) => Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) _x s)] (b : Int) (Hb : forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe z b)) (Hinh : Exists.{1} Int (fun (z : Int) => Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s)), Eq.{1} Int (SupSet.supₛ.{0} Int (ConditionallyCompleteLattice.toHasSup.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int Int.conditionallyCompleteLinearOrder)) s) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Subtype.{1} Int (fun (ub : Int) => And (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) ub s) (forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe z ub)))) Int (HasLiftT.mk.{1, 1} (Subtype.{1} Int (fun (ub : Int) => And (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) ub s) (forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe z ub)))) Int (CoeTCₓ.coe.{1, 1} (Subtype.{1} Int (fun (ub : Int) => And (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) ub s) (forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe z ub)))) Int (coeBase.{1, 1} (Subtype.{1} Int (fun (ub : Int) => And (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) ub s) (forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe z ub)))) Int (coeSubtype.{1} Int (fun (ub : Int) => And (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) ub s) (forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe z ub))))))) (Int.greatestOfBdd (fun (z : Int) => Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) (fun (a : Int) => _inst_1 a) b Hb Hinh))
but is expected to have type
  forall {s : Set.{0} Int} [_inst_1 : DecidablePred.{1} Int (fun (_x : Int) => Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) _x s)] (b : Int) (Hb : forall (z : Int), (Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) z s) -> (LE.le.{0} Int Int.instLEInt z b)) (Hinh : Exists.{1} Int (fun (z : Int) => Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) z s)), Eq.{1} Int (SupSet.supₛ.{0} Int (ConditionallyCompleteLattice.toSupSet.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int instConditionallyCompleteLinearOrderInt)) s) (Subtype.val.{1} Int (fun (ub : Int) => And (Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) ub s) (forall (z : Int), (Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) z s) -> (LE.le.{0} Int Int.instLEInt z ub))) (Int.greatestOfBdd (fun (z : Int) => Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) z s) (fun (a : Int) => _inst_1 a) b Hb Hinh))
Case conversion may be inaccurate. Consider using '#align int.cSup_eq_greatest_of_bdd Int.csupₛ_eq_greatest_of_bddₓ'. -/
theorem csupₛ_eq_greatest_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b)
    (Hinh : ∃ z : ℤ, z ∈ s) : supₛ s = greatestOfBdd b Hb Hinh :=
  by
  convert dif_pos _ using 1
  · convert coe_greatest_of_bdd_eq _ (Classical.choose_spec (⟨b, Hb⟩ : BddAbove s)) _
  · exact ⟨Hinh, b, Hb⟩
#align int.cSup_eq_greatest_of_bdd Int.csupₛ_eq_greatest_of_bdd

/- warning: int.cSup_empty -> Int.csupₛ_empty is a dubious translation:
lean 3 declaration is
  Eq.{1} Int (SupSet.supₛ.{0} Int (ConditionallyCompleteLattice.toHasSup.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int Int.conditionallyCompleteLinearOrder)) (EmptyCollection.emptyCollection.{0} (Set.{0} Int) (Set.hasEmptyc.{0} Int))) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))
but is expected to have type
  Eq.{1} Int (SupSet.supₛ.{0} Int (ConditionallyCompleteLattice.toSupSet.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int instConditionallyCompleteLinearOrderInt)) (EmptyCollection.emptyCollection.{0} (Set.{0} Int) (Set.instEmptyCollectionSet.{0} Int))) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))
Case conversion may be inaccurate. Consider using '#align int.cSup_empty Int.csupₛ_emptyₓ'. -/
@[simp]
theorem csupₛ_empty : supₛ (∅ : Set ℤ) = 0 :=
  dif_neg (by simp)
#align int.cSup_empty Int.csupₛ_empty

/- warning: int.cSup_of_not_bdd_above -> Int.csupₛ_of_not_bdd_above is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Int}, (Not (BddAbove.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) s)) -> (Eq.{1} Int (SupSet.supₛ.{0} Int (ConditionallyCompleteLattice.toHasSup.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int Int.conditionallyCompleteLinearOrder)) s) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {s : Set.{0} Int}, (Not (BddAbove.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) s)) -> (Eq.{1} Int (SupSet.supₛ.{0} Int (ConditionallyCompleteLattice.toSupSet.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int instConditionallyCompleteLinearOrderInt)) s) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align int.cSup_of_not_bdd_above Int.csupₛ_of_not_bdd_aboveₓ'. -/
theorem csupₛ_of_not_bdd_above {s : Set ℤ} (h : ¬BddAbove s) : supₛ s = 0 :=
  dif_neg (by simp [h])
#align int.cSup_of_not_bdd_above Int.csupₛ_of_not_bdd_above

/- warning: int.cInf_eq_least_of_bdd -> Int.cinfₛ_eq_least_of_bdd is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Int} [_inst_1 : DecidablePred.{1} Int (fun (_x : Int) => Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) _x s)] (b : Int) (Hb : forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe b z)) (Hinh : Exists.{1} Int (fun (z : Int) => Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s)), Eq.{1} Int (InfSet.infₛ.{0} Int (ConditionallyCompleteLattice.toHasInf.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int Int.conditionallyCompleteLinearOrder)) s) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Subtype.{1} Int (fun (lb : Int) => And (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) lb s) (forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe lb z)))) Int (HasLiftT.mk.{1, 1} (Subtype.{1} Int (fun (lb : Int) => And (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) lb s) (forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe lb z)))) Int (CoeTCₓ.coe.{1, 1} (Subtype.{1} Int (fun (lb : Int) => And (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) lb s) (forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe lb z)))) Int (coeBase.{1, 1} (Subtype.{1} Int (fun (lb : Int) => And (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) lb s) (forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe lb z)))) Int (coeSubtype.{1} Int (fun (lb : Int) => And (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) lb s) (forall (z : Int), (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) -> (LE.le.{0} Int Int.hasLe lb z))))))) (Int.leastOfBdd (fun (z : Int) => Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) z s) (fun (a : Int) => _inst_1 a) b Hb Hinh))
but is expected to have type
  forall {s : Set.{0} Int} [_inst_1 : DecidablePred.{1} Int (fun (_x : Int) => Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) _x s)] (b : Int) (Hb : forall (z : Int), (Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) z s) -> (LE.le.{0} Int Int.instLEInt b z)) (Hinh : Exists.{1} Int (fun (z : Int) => Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) z s)), Eq.{1} Int (InfSet.infₛ.{0} Int (ConditionallyCompleteLattice.toInfSet.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int instConditionallyCompleteLinearOrderInt)) s) (Subtype.val.{1} Int (fun (lb : Int) => And (Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) lb s) (forall (z : Int), (Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) z s) -> (LE.le.{0} Int Int.instLEInt lb z))) (Int.leastOfBdd (fun (z : Int) => Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) z s) (fun (a : Int) => _inst_1 a) b Hb Hinh))
Case conversion may be inaccurate. Consider using '#align int.cInf_eq_least_of_bdd Int.cinfₛ_eq_least_of_bddₓ'. -/
theorem cinfₛ_eq_least_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z)
    (Hinh : ∃ z : ℤ, z ∈ s) : infₛ s = leastOfBdd b Hb Hinh :=
  by
  convert dif_pos _ using 1
  · convert coe_least_of_bdd_eq _ (Classical.choose_spec (⟨b, Hb⟩ : BddBelow s)) _
  · exact ⟨Hinh, b, Hb⟩
#align int.cInf_eq_least_of_bdd Int.cinfₛ_eq_least_of_bdd

/- warning: int.cInf_empty -> Int.cinfₛ_empty is a dubious translation:
lean 3 declaration is
  Eq.{1} Int (InfSet.infₛ.{0} Int (ConditionallyCompleteLattice.toHasInf.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int Int.conditionallyCompleteLinearOrder)) (EmptyCollection.emptyCollection.{0} (Set.{0} Int) (Set.hasEmptyc.{0} Int))) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))
but is expected to have type
  Eq.{1} Int (InfSet.infₛ.{0} Int (ConditionallyCompleteLattice.toInfSet.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int instConditionallyCompleteLinearOrderInt)) (EmptyCollection.emptyCollection.{0} (Set.{0} Int) (Set.instEmptyCollectionSet.{0} Int))) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))
Case conversion may be inaccurate. Consider using '#align int.cInf_empty Int.cinfₛ_emptyₓ'. -/
@[simp]
theorem cinfₛ_empty : infₛ (∅ : Set ℤ) = 0 :=
  dif_neg (by simp)
#align int.cInf_empty Int.cinfₛ_empty

/- warning: int.cInf_of_not_bdd_below -> Int.cinfₛ_of_not_bdd_below is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Int}, (Not (BddBelow.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) s)) -> (Eq.{1} Int (InfSet.infₛ.{0} Int (ConditionallyCompleteLattice.toHasInf.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int Int.conditionallyCompleteLinearOrder)) s) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {s : Set.{0} Int}, (Not (BddBelow.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) s)) -> (Eq.{1} Int (InfSet.infₛ.{0} Int (ConditionallyCompleteLattice.toInfSet.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int instConditionallyCompleteLinearOrderInt)) s) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align int.cInf_of_not_bdd_below Int.cinfₛ_of_not_bdd_belowₓ'. -/
theorem cinfₛ_of_not_bdd_below {s : Set ℤ} (h : ¬BddBelow s) : infₛ s = 0 :=
  dif_neg (by simp [h])
#align int.cInf_of_not_bdd_below Int.cinfₛ_of_not_bdd_below

/- warning: int.cSup_mem -> Int.csupₛ_mem is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Int}, (Set.Nonempty.{0} Int s) -> (BddAbove.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) s) -> (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) (SupSet.supₛ.{0} Int (ConditionallyCompleteLattice.toHasSup.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int Int.conditionallyCompleteLinearOrder)) s) s)
but is expected to have type
  forall {s : Set.{0} Int}, (Set.Nonempty.{0} Int s) -> (BddAbove.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) s) -> (Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) (SupSet.supₛ.{0} Int (ConditionallyCompleteLattice.toSupSet.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int instConditionallyCompleteLinearOrderInt)) s) s)
Case conversion may be inaccurate. Consider using '#align int.cSup_mem Int.csupₛ_memₓ'. -/
theorem csupₛ_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddAbove s) : supₛ s ∈ s :=
  by
  convert (greatest_of_bdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩
#align int.cSup_mem Int.csupₛ_mem

/- warning: int.cInf_mem -> Int.cinfₛ_mem is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Int}, (Set.Nonempty.{0} Int s) -> (BddBelow.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) s) -> (Membership.Mem.{0, 0} Int (Set.{0} Int) (Set.hasMem.{0} Int) (InfSet.infₛ.{0} Int (ConditionallyCompleteLattice.toHasInf.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int Int.conditionallyCompleteLinearOrder)) s) s)
but is expected to have type
  forall {s : Set.{0} Int}, (Set.Nonempty.{0} Int s) -> (BddBelow.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) s) -> (Membership.mem.{0, 0} Int (Set.{0} Int) (Set.instMembershipSet.{0} Int) (InfSet.infₛ.{0} Int (ConditionallyCompleteLattice.toInfSet.{0} Int (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int instConditionallyCompleteLinearOrderInt)) s) s)
Case conversion may be inaccurate. Consider using '#align int.cInf_mem Int.cinfₛ_memₓ'. -/
theorem cinfₛ_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddBelow s) : infₛ s ∈ s :=
  by
  convert (least_of_bdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩
#align int.cInf_mem Int.cinfₛ_mem

end Int

