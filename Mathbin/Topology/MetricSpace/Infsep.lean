/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson

! This file was ported from Lean 3 source module topology.metric_space.infsep
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.Basic

/-!
# Infimum separation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the extended infimum separation of a set. This is approximately dual to the
diameter of a set, but where the extended diameter of a set is the supremum of the extended distance
between elements of the set, the extended infimum separation is the infimum of the (extended)
distance between *distinct* elements in the set.

We also define the infimum separation as the cast of the extended infimum separation to the reals.
This is the infimum of the distance between distinct elements of the set when in a pseudometric
space.

All lemmas and definitions are in the `set` namespace to give access to dot notation.

## Main definitions
* `set.einfsep`: Extended infimum separation of a set.
* `set.infsep`: Infimum separation of a set (when in a pseudometric space).

!-/


variable {α β : Type _}

namespace Set

section Einfsep

open ENNReal

open Function

#print Set.einfsep /-
/-- The "extended infimum separation" of a set with an edist function. -/
noncomputable def einfsep [EDist α] (s : Set α) : ℝ≥0∞ :=
  ⨅ (x ∈ s) (y ∈ s) (hxy : x ≠ y), edist x y
#align set.einfsep Set.einfsep
-/

section EDist

variable [EDist α] {x y : α} {s t : Set α}

/- warning: set.le_einfsep_iff -> Set.le_einfsep_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {d : ENNReal}, Iff (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) d (Set.einfsep.{u1} α _inst_1 s)) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) d (EDist.edist.{u1} α _inst_1 x y))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {d : ENNReal}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) d (Set.einfsep.{u1} α _inst_1 s)) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) d (EDist.edist.{u1} α _inst_1 x y))))
Case conversion may be inaccurate. Consider using '#align set.le_einfsep_iff Set.le_einfsep_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem le_einfsep_iff {d} :
    d ≤ s.einfsep ↔ ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s) (hxy : x ≠ y), d ≤ edist x y := by
  simp_rw [einfsep, le_iInf_iff]
#align set.le_einfsep_iff Set.le_einfsep_iff

/- warning: set.einfsep_zero -> Set.einfsep_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (forall (C : ENNReal), (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) C) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => Exists.{0} (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α _inst_1 x y) C)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall (C : ENNReal), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) C) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) => Exists.{0} (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α _inst_1 x y) C)))))))
Case conversion may be inaccurate. Consider using '#align set.einfsep_zero Set.einfsep_zeroₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem einfsep_zero :
    s.einfsep = 0 ↔
      ∀ (C) (hC : 0 < C), ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s)(hxy : x ≠ y), edist x y < C :=
  by simp_rw [einfsep, ← bot_eq_zero, iInf_eq_bot, iInf_lt_iff]
#align set.einfsep_zero Set.einfsep_zero

/- warning: set.einfsep_pos -> Set.einfsep_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (Set.einfsep.{u1} α _inst_1 s)) (Exists.{1} ENNReal (fun (C : ENNReal) => Exists.{0} (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) C) (fun (hC : LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) C) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) C (EDist.edist.{u1} α _inst_1 x y))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (Set.einfsep.{u1} α _inst_1 s)) (Exists.{1} ENNReal (fun (C : ENNReal) => Exists.{0} (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) C) (fun (hC : LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) C) => forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) C (EDist.edist.{u1} α _inst_1 x y))))))
Case conversion may be inaccurate. Consider using '#align set.einfsep_pos Set.einfsep_posₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem einfsep_pos :
    0 < s.einfsep ↔
      ∃ (C : _)(hC : 0 < C), ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s) (hxy : x ≠ y), C ≤ edist x y :=
  by
  rw [pos_iff_ne_zero, Ne.def, einfsep_zero]
  simp only [not_forall, not_exists, not_lt]
#align set.einfsep_pos Set.einfsep_pos

/- warning: set.einfsep_top -> Set.einfsep_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (Eq.{1} ENNReal (EDist.edist.{u1} α _inst_1 x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (Eq.{1} ENNReal (EDist.edist.{u1} α _inst_1 x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))))
Case conversion may be inaccurate. Consider using '#align set.einfsep_top Set.einfsep_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem einfsep_top :
    s.einfsep = ∞ ↔ ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s) (hxy : x ≠ y), edist x y = ∞ := by
  simp_rw [einfsep, iInf_eq_top]
#align set.einfsep_top Set.einfsep_top

/- warning: set.einfsep_lt_top -> Set.einfsep_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => Exists.{0} (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α _inst_1 x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) => Exists.{0} (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α _inst_1 x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))))))
Case conversion may be inaccurate. Consider using '#align set.einfsep_lt_top Set.einfsep_lt_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem einfsep_lt_top :
    s.einfsep < ∞ ↔ ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s)(hxy : x ≠ y), edist x y < ∞ := by
  simp_rw [einfsep, iInf_lt_iff]
#align set.einfsep_lt_top Set.einfsep_lt_top

/- warning: set.einfsep_ne_top -> Set.einfsep_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (Ne.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => Exists.{0} (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => Ne.{1} ENNReal (EDist.edist.{u1} α _inst_1 x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (Ne.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) => Exists.{0} (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => Ne.{1} ENNReal (EDist.edist.{u1} α _inst_1 x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))))))
Case conversion may be inaccurate. Consider using '#align set.einfsep_ne_top Set.einfsep_ne_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem einfsep_ne_top :
    s.einfsep ≠ ∞ ↔ ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s)(hxy : x ≠ y), edist x y ≠ ∞ := by
  simp_rw [← lt_top_iff_ne_top, einfsep_lt_top]
#align set.einfsep_ne_top Set.einfsep_ne_top

/- warning: set.einfsep_lt_iff -> Set.einfsep_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {d : ENNReal}, Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α _inst_1 s) d) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => Exists.{0} (Ne.{succ u1} α x y) (fun (h : Ne.{succ u1} α x y) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α _inst_1 x y) d))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {d : ENNReal}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α _inst_1 s) d) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) => Exists.{0} (Ne.{succ u1} α x y) (fun (h : Ne.{succ u1} α x y) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α _inst_1 x y) d))))))
Case conversion may be inaccurate. Consider using '#align set.einfsep_lt_iff Set.einfsep_lt_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem einfsep_lt_iff {d} :
    s.einfsep < d ↔ ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s)(h : x ≠ y), edist x y < d := by
  simp_rw [einfsep, iInf_lt_iff]
#align set.einfsep_lt_iff Set.einfsep_lt_iff

/- warning: set.nontrivial_of_einfsep_lt_top -> Set.nontrivial_of_einfsep_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Set.Nontrivial.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Set.Nontrivial.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.nontrivial_of_einfsep_lt_top Set.nontrivial_of_einfsep_lt_topₓ'. -/
theorem nontrivial_of_einfsep_lt_top (hs : s.einfsep < ∞) : s.Nontrivial :=
  by
  rcases einfsep_lt_top.1 hs with ⟨_, hx, _, hy, hxy, _⟩
  exact ⟨_, hx, _, hy, hxy⟩
#align set.nontrivial_of_einfsep_lt_top Set.nontrivial_of_einfsep_lt_top

/- warning: set.nontrivial_of_einfsep_ne_top -> Set.nontrivial_of_einfsep_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, (Ne.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Set.Nontrivial.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, (Ne.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Set.Nontrivial.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.nontrivial_of_einfsep_ne_top Set.nontrivial_of_einfsep_ne_topₓ'. -/
theorem nontrivial_of_einfsep_ne_top (hs : s.einfsep ≠ ∞) : s.Nontrivial :=
  nontrivial_of_einfsep_lt_top (lt_top_iff_ne_top.mpr hs)
#align set.nontrivial_of_einfsep_ne_top Set.nontrivial_of_einfsep_ne_top

/- warning: set.subsingleton.einfsep -> Set.Subsingleton.einfsep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align set.subsingleton.einfsep Set.Subsingleton.einfsepₓ'. -/
theorem Subsingleton.einfsep (hs : s.Subsingleton) : s.einfsep = ∞ :=
  by
  rw [einfsep_top]
  exact fun _ hx _ hy hxy => (hxy <| hs hx hy).elim
#align set.subsingleton.einfsep Set.Subsingleton.einfsep

/- warning: set.le_einfsep_image_iff -> Set.le_einfsep_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : EDist.{u1} α] {d : ENNReal} {f : β -> α} {s : Set.{u2} β}, Iff (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) d (Set.einfsep.{u1} α _inst_1 (Set.image.{u2, u1} β α f s))) (forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) -> (forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y s) -> (Ne.{succ u1} α (f x) (f y)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) d (EDist.edist.{u1} α _inst_1 (f x) (f y)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : EDist.{u1} α] {d : ENNReal} {f : β -> α} {s : Set.{u2} β}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) d (Set.einfsep.{u1} α _inst_1 (Set.image.{u2, u1} β α f s))) (forall (x : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) -> (forall (y : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) y s) -> (Ne.{succ u1} α (f x) (f y)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) d (EDist.edist.{u1} α _inst_1 (f x) (f y)))))
Case conversion may be inaccurate. Consider using '#align set.le_einfsep_image_iff Set.le_einfsep_image_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem le_einfsep_image_iff {d} {f : β → α} {s : Set β} :
    d ≤ einfsep (f '' s) ↔ ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), f x ≠ f y → d ≤ edist (f x) (f y) :=
  by simp_rw [le_einfsep_iff, ball_image_iff]
#align set.le_einfsep_image_iff Set.le_einfsep_image_iff

/- warning: set.le_edist_of_le_einfsep -> Set.le_edist_of_le_einfsep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {d : ENNReal} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall {y : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) d (Set.einfsep.{u1} α _inst_1 s)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) d (EDist.edist.{u1} α _inst_1 x y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {d : ENNReal} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall {y : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) d (Set.einfsep.{u1} α _inst_1 s)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) d (EDist.edist.{u1} α _inst_1 x y)))
Case conversion may be inaccurate. Consider using '#align set.le_edist_of_le_einfsep Set.le_edist_of_le_einfsepₓ'. -/
theorem le_edist_of_le_einfsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ s.einfsep) : d ≤ edist x y :=
  le_einfsep_iff.1 hd x hx y hy hxy
#align set.le_edist_of_le_einfsep Set.le_edist_of_le_einfsep

/- warning: set.einfsep_le_edist_of_mem -> Set.einfsep_le_edist_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall {y : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α _inst_1 s) (EDist.edist.{u1} α _inst_1 x y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall {y : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α _inst_1 s) (EDist.edist.{u1} α _inst_1 x y)))
Case conversion may be inaccurate. Consider using '#align set.einfsep_le_edist_of_mem Set.einfsep_le_edist_of_memₓ'. -/
theorem einfsep_le_edist_of_mem {x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y) :
    s.einfsep ≤ edist x y :=
  le_edist_of_le_einfsep hx hy hxy le_rfl
#align set.einfsep_le_edist_of_mem Set.einfsep_le_edist_of_mem

/- warning: set.einfsep_le_of_mem_of_edist_le -> Set.einfsep_le_of_mem_of_edist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {d : ENNReal} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall {y : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α _inst_1 x y) d) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α _inst_1 s) d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {d : ENNReal} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall {y : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α _inst_1 x y) d) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α _inst_1 s) d))
Case conversion may be inaccurate. Consider using '#align set.einfsep_le_of_mem_of_edist_le Set.einfsep_le_of_mem_of_edist_leₓ'. -/
theorem einfsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : edist x y ≤ d) : s.einfsep ≤ d :=
  le_trans (einfsep_le_edist_of_mem hx hy hxy) hxy'
#align set.einfsep_le_of_mem_of_edist_le Set.einfsep_le_of_mem_of_edist_le

/- warning: set.le_einfsep -> Set.le_einfsep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {d : ENNReal}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) d (EDist.edist.{u1} α _inst_1 x y)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) d (Set.einfsep.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {d : ENNReal}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) d (EDist.edist.{u1} α _inst_1 x y)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) d (Set.einfsep.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align set.le_einfsep Set.le_einfsepₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem le_einfsep {d} (h : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s) (hxy : x ≠ y), d ≤ edist x y) :
    d ≤ s.einfsep :=
  le_einfsep_iff.2 h
#align set.le_einfsep Set.le_einfsep

/- warning: set.einfsep_empty -> Set.einfsep_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α], Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α], Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align set.einfsep_empty Set.einfsep_emptyₓ'. -/
@[simp]
theorem einfsep_empty : (∅ : Set α).einfsep = ∞ :=
  subsingleton_empty.einfsep
#align set.einfsep_empty Set.einfsep_empty

/- warning: set.einfsep_singleton -> Set.einfsep_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α}, Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α}, Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align set.einfsep_singleton Set.einfsep_singletonₓ'. -/
@[simp]
theorem einfsep_singleton : ({x} : Set α).einfsep = ∞ :=
  subsingleton_singleton.einfsep
#align set.einfsep_singleton Set.einfsep_singleton

/- warning: set.einfsep_Union_mem_option -> Set.einfsep_iUnion_mem_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {ι : Type.{u2}} (o : Option.{u2} ι) (s : ι -> (Set.{u1} α)), Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Option.{u2} ι) (Option.hasMem.{u2} ι) i o) (fun (H : Membership.Mem.{u2, u2} ι (Option.{u2} ι) (Option.hasMem.{u2} ι) i o) => s i)))) (iInf.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u2, u2} ι (Option.{u2} ι) (Option.hasMem.{u2} ι) i o) (fun (H : Membership.Mem.{u2, u2} ι (Option.{u2} ι) (Option.hasMem.{u2} ι) i o) => Set.einfsep.{u1} α _inst_1 (s i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {ι : Type.{u2}} (o : Option.{u2} ι) (s : ι -> (Set.{u1} α)), Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} ι (Option.{u2} ι) (Option.instMembershipOption.{u2} ι) i o) (fun (H : Membership.mem.{u2, u2} ι (Option.{u2} ι) (Option.instMembershipOption.{u2} ι) i o) => s i)))) (iInf.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u2, u2} ι (Option.{u2} ι) (Option.instMembershipOption.{u2} ι) i o) (fun (H : Membership.mem.{u2, u2} ι (Option.{u2} ι) (Option.instMembershipOption.{u2} ι) i o) => Set.einfsep.{u1} α _inst_1 (s i))))
Case conversion may be inaccurate. Consider using '#align set.einfsep_Union_mem_option Set.einfsep_iUnion_mem_optionₓ'. -/
theorem einfsep_iUnion_mem_option {ι : Type _} (o : Option ι) (s : ι → Set α) :
    (⋃ i ∈ o, s i).einfsep = ⨅ i ∈ o, (s i).einfsep := by cases o <;> simp
#align set.einfsep_Union_mem_option Set.einfsep_iUnion_mem_option

/- warning: set.einfsep_anti -> Set.einfsep_anti is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α _inst_1 t) (Set.einfsep.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α _inst_1 t) (Set.einfsep.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align set.einfsep_anti Set.einfsep_antiₓ'. -/
theorem einfsep_anti (hst : s ⊆ t) : t.einfsep ≤ s.einfsep :=
  le_einfsep fun x hx y hy => einfsep_le_edist_of_mem (hst hx) (hst hy)
#align set.einfsep_anti Set.einfsep_anti

/- warning: set.einfsep_insert_le -> Set.einfsep_insert_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {s : Set.{u1} α}, LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s)) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) α (fun (y : α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => EDist.edist.{u1} α _inst_1 x y))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {s : Set.{u1} α}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x s)) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) α (fun (y : α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => EDist.edist.{u1} α _inst_1 x y))))
Case conversion may be inaccurate. Consider using '#align set.einfsep_insert_le Set.einfsep_insert_leₓ'. -/
theorem einfsep_insert_le : (insert x s).einfsep ≤ ⨅ (y ∈ s) (hxy : x ≠ y), edist x y :=
  by
  simp_rw [le_iInf_iff]
  refine' fun _ hy hxy => einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ hy) hxy
#align set.einfsep_insert_le Set.einfsep_insert_le

/- warning: set.le_einfsep_pair -> Set.le_einfsep_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {y : α}, LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Inf.inf.{0} ENNReal (SemilatticeInf.toHasInf.{0} ENNReal (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α _inst_1 x y) (EDist.edist.{u1} α _inst_1 y x)) (Set.einfsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {y : α}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Inf.inf.{0} ENNReal (Lattice.toInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α _inst_1 x y) (EDist.edist.{u1} α _inst_1 y x)) (Set.einfsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) y)))
Case conversion may be inaccurate. Consider using '#align set.le_einfsep_pair Set.le_einfsep_pairₓ'. -/
theorem le_einfsep_pair : edist x y ⊓ edist y x ≤ ({x, y} : Set α).einfsep :=
  by
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff]
  rintro a (rfl | rfl) b (rfl | rfl) hab <;> finish
#align set.le_einfsep_pair Set.le_einfsep_pair

/- warning: set.einfsep_pair_le_left -> Set.einfsep_pair_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {y : α}, (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) y))) (EDist.edist.{u1} α _inst_1 x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {y : α}, (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) y))) (EDist.edist.{u1} α _inst_1 x y))
Case conversion may be inaccurate. Consider using '#align set.einfsep_pair_le_left Set.einfsep_pair_le_leftₓ'. -/
theorem einfsep_pair_le_left (hxy : x ≠ y) : ({x, y} : Set α).einfsep ≤ edist x y :=
  einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy
#align set.einfsep_pair_le_left Set.einfsep_pair_le_left

/- warning: set.einfsep_pair_le_right -> Set.einfsep_pair_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {y : α}, (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) y))) (EDist.edist.{u1} α _inst_1 y x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {y : α}, (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) y))) (EDist.edist.{u1} α _inst_1 y x))
Case conversion may be inaccurate. Consider using '#align set.einfsep_pair_le_right Set.einfsep_pair_le_rightₓ'. -/
theorem einfsep_pair_le_right (hxy : x ≠ y) : ({x, y} : Set α).einfsep ≤ edist y x := by
  rw [pair_comm] <;> exact einfsep_pair_le_left hxy.symm
#align set.einfsep_pair_le_right Set.einfsep_pair_le_right

/- warning: set.einfsep_pair_eq_inf -> Set.einfsep_pair_eq_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {y : α}, (Ne.{succ u1} α x y) -> (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) y))) (Inf.inf.{0} ENNReal (SemilatticeInf.toHasInf.{0} ENNReal (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α _inst_1 x y) (EDist.edist.{u1} α _inst_1 y x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {y : α}, (Ne.{succ u1} α x y) -> (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) y))) (Inf.inf.{0} ENNReal (Lattice.toInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α _inst_1 x y) (EDist.edist.{u1} α _inst_1 y x)))
Case conversion may be inaccurate. Consider using '#align set.einfsep_pair_eq_inf Set.einfsep_pair_eq_infₓ'. -/
theorem einfsep_pair_eq_inf (hxy : x ≠ y) : ({x, y} : Set α).einfsep = edist x y ⊓ edist y x :=
  le_antisymm (le_inf (einfsep_pair_le_left hxy) (einfsep_pair_le_right hxy)) le_einfsep_pair
#align set.einfsep_pair_eq_inf Set.einfsep_pair_eq_inf

/- warning: set.einfsep_eq_infi -> Set.einfsep_eq_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (fun (d : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) => Function.uncurry.{u1, u1, 0} α α ENNReal (EDist.edist.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (coeSubtype.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) x (Set.offDiag.{u1} α s)))))) d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) (fun (d : Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) => Function.uncurry.{u1, u1, 0} α α ENNReal (EDist.edist.{u1} α _inst_1) (Subtype.val.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) x (Set.offDiag.{u1} α s)) d)))
Case conversion may be inaccurate. Consider using '#align set.einfsep_eq_infi Set.einfsep_eq_iInfₓ'. -/
theorem einfsep_eq_iInf : s.einfsep = ⨅ d : s.offDiag, (uncurry edist) (d : α × α) :=
  by
  refine' eq_of_forall_le_iff fun _ => _
  simp_rw [le_einfsep_iff, le_iInf_iff, imp_forall_iff, SetCoe.forall, Subtype.coe_mk, mem_off_diag,
    Prod.forall, uncurry_apply_pair, and_imp]
#align set.einfsep_eq_infi Set.einfsep_eq_iInf

/- warning: set.einfsep_of_fintype -> Set.einfsep_of_fintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)], Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Finset.inf.{0, u1} ENNReal (Prod.{u1, u1} α α) (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (LinearOrderedAddCommMonoidWithTop.toOrderTop.{0} ENNReal ENNReal.linearOrderedAddCommMonoidWithTop) (Set.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s _inst_3)) (Function.uncurry.{u1, u1, 0} α α ENNReal (EDist.edist.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : Fintype.{u1} (Set.Elem.{u1} α s)], Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Finset.inf.{0, u1} ENNReal (Prod.{u1, u1} α α) (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (BoundedOrder.toOrderTop.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (SemilatticeInf.toPartialOrder.{0} ENNReal (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))))) ENNReal.instBoundedOrderENNRealToLEToPreorderToPartialOrderToSemilatticeInfToLatticeInstENNRealDistribLattice) (Set.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s _inst_3)) (Function.uncurry.{u1, u1, 0} α α ENNReal (EDist.edist.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.einfsep_of_fintype Set.einfsep_of_fintypeₓ'. -/
theorem einfsep_of_fintype [DecidableEq α] [Fintype s] :
    s.einfsep = s.offDiag.toFinset.inf (uncurry edist) :=
  by
  refine' eq_of_forall_le_iff fun _ => _
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, mem_to_finset, mem_off_diag,
    Prod.forall, uncurry_apply_pair, and_imp]
#align set.einfsep_of_fintype Set.einfsep_of_fintype

/- warning: set.finite.einfsep -> Set.Finite.einfsep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} (hs : Set.Finite.{u1} α s), Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Finset.inf.{0, u1} ENNReal (Prod.{u1, u1} α α) (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (LinearOrderedAddCommMonoidWithTop.toOrderTop.{0} ENNReal ENNReal.linearOrderedAddCommMonoidWithTop) (Set.Finite.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hs)) (Function.uncurry.{u1, u1, 0} α α ENNReal (EDist.edist.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α} (hs : Set.Finite.{u1} α s), Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Finset.inf.{0, u1} ENNReal (Prod.{u1, u1} α α) (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (BoundedOrder.toOrderTop.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (SemilatticeInf.toPartialOrder.{0} ENNReal (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))))) ENNReal.instBoundedOrderENNRealToLEToPreorderToPartialOrderToSemilatticeInfToLatticeInstENNRealDistribLattice) (Set.Finite.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hs)) (Function.uncurry.{u1, u1, 0} α α ENNReal (EDist.edist.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.finite.einfsep Set.Finite.einfsepₓ'. -/
theorem Finite.einfsep (hs : s.Finite) : s.einfsep = hs.offDiag.toFinset.inf (uncurry edist) :=
  by
  refine' eq_of_forall_le_iff fun _ => _
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, finite.mem_to_finset, mem_off_diag,
    Prod.forall, uncurry_apply_pair, and_imp]
#align set.finite.einfsep Set.Finite.einfsep

/- warning: set.finset.coe_einfsep -> Set.Finset.coe_einfsep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (Finset.inf.{0, u1} ENNReal (Prod.{u1, u1} α α) (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (LinearOrderedAddCommMonoidWithTop.toOrderTop.{0} ENNReal ENNReal.linearOrderedAddCommMonoidWithTop) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s) (Function.uncurry.{u1, u1, 0} α α ENNReal (EDist.edist.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 (Finset.toSet.{u1} α s)) (Finset.inf.{0, u1} ENNReal (Prod.{u1, u1} α α) (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (BoundedOrder.toOrderTop.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (SemilatticeInf.toPartialOrder.{0} ENNReal (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))))) ENNReal.instBoundedOrderENNRealToLEToPreorderToPartialOrderToSemilatticeInfToLatticeInstENNRealDistribLattice) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s) (Function.uncurry.{u1, u1, 0} α α ENNReal (EDist.edist.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.finset.coe_einfsep Set.Finset.coe_einfsepₓ'. -/
theorem Finset.coe_einfsep [DecidableEq α] {s : Finset α} :
    (s : Set α).einfsep = s.offDiag.inf (uncurry edist) := by
  simp_rw [einfsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]
#align set.finset.coe_einfsep Set.Finset.coe_einfsep

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
#print Set.Nontrivial.einfsep_exists_of_finite /-
theorem Nontrivial.einfsep_exists_of_finite [Finite s] (hs : s.Nontrivial) :
    ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s)(hxy : x ≠ y), s.einfsep = edist x y := by
  classical
    cases nonempty_fintype s
    simp_rw [einfsep_of_fintype]
    rcases@Finset.exists_mem_eq_inf _ _ _ _ s.off_diag.to_finset (by simpa) (uncurry edist) with
      ⟨_, hxy, hed⟩
    simp_rw [mem_to_finset] at hxy
    refine' ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩
#align set.nontrivial.einfsep_exists_of_finite Set.Nontrivial.einfsep_exists_of_finite
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
#print Set.Finite.einfsep_exists_of_nontrivial /-
theorem Finite.einfsep_exists_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s)(hxy : x ≠ y), s.einfsep = edist x y :=
  letI := hsf.fintype
  hs.einfsep_exists_of_finite
#align set.finite.einfsep_exists_of_nontrivial Set.Finite.einfsep_exists_of_nontrivial
-/

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y z : α} {s t : Set α}

#print Set.einfsep_pair /-
theorem einfsep_pair (hxy : x ≠ y) : ({x, y} : Set α).einfsep = edist x y :=
  by
  nth_rw 1 [← min_self (edist x y)]
  convert einfsep_pair_eq_inf hxy using 2
  rw [edist_comm]
#align set.einfsep_pair Set.einfsep_pair
-/

/- warning: set.einfsep_insert -> Set.einfsep_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Eq.{1} ENNReal (Set.einfsep.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s)) (Inf.inf.{0} ENNReal (SemilatticeInf.toHasInf.{0} ENNReal (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) α (fun (y : α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y)))) (Set.einfsep.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Eq.{1} ENNReal (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x s)) (Inf.inf.{0} ENNReal (Lattice.toInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) α (fun (y : α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y)))) (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align set.einfsep_insert Set.einfsep_insertₓ'. -/
theorem einfsep_insert : einfsep (insert x s) = (⨅ (y ∈ s) (hxy : x ≠ y), edist x y) ⊓ s.einfsep :=
  by
  refine' le_antisymm (le_min einfsep_insert_le (einfsep_anti (subset_insert _ _))) _
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff]
  rintro y (rfl | hy) z (rfl | hz) hyz
  · exact False.elim (hyz rfl)
  · exact Or.inl (iInf_le_of_le _ (iInf₂_le hz hyz))
  · rw [edist_comm]
    exact Or.inl (iInf_le_of_le _ (iInf₂_le hy hyz.symm))
  · exact Or.inr (einfsep_le_edist_of_mem hy hz hyz)
#align set.einfsep_insert Set.einfsep_insert

/- warning: set.einfsep_triple -> Set.einfsep_triple is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {z : α}, (Ne.{succ u1} α x y) -> (Ne.{succ u1} α y z) -> (Ne.{succ u1} α x z) -> (Eq.{1} ENNReal (Set.einfsep.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) y (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) z)))) (Inf.inf.{0} ENNReal (SemilatticeInf.toHasInf.{0} ENNReal (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Inf.inf.{0} ENNReal (SemilatticeInf.toHasInf.{0} ENNReal (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x z)) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) y z)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {z : α}, (Ne.{succ u1} α x y) -> (Ne.{succ u1} α y z) -> (Ne.{succ u1} α x z) -> (Eq.{1} ENNReal (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) y (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) z)))) (Inf.inf.{0} ENNReal (Lattice.toInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Inf.inf.{0} ENNReal (Lattice.toInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x z)) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) y z)))
Case conversion may be inaccurate. Consider using '#align set.einfsep_triple Set.einfsep_tripleₓ'. -/
theorem einfsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    einfsep ({x, y, z} : Set α) = edist x y ⊓ edist x z ⊓ edist y z := by
  simp_rw [einfsep_insert, iInf_insert, iInf_singleton, einfsep_singleton, inf_top_eq,
    ciInf_pos hxy, ciInf_pos hyz, ciInf_pos hxz]
#align set.einfsep_triple Set.einfsep_triple

/- warning: set.le_einfsep_pi_of_le -> Set.le_einfsep_pi_of_le is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoEMetricSpace.{u2} (π b)] {s : forall (b : β), Set.{u2} (π b)} {c : ENNReal}, (forall (b : β), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) c (Set.einfsep.{u2} (π b) (PseudoEMetricSpace.toHasEdist.{u2} (π b) (_inst_3 b)) (s b))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) c (Set.einfsep.{max u1 u2} (forall (i : β), π i) (PseudoEMetricSpace.toHasEdist.{max u1 u2} (forall (i : β), π i) (pseudoEMetricSpacePi.{u1, u2} β (fun (i : β) => π i) _inst_2 (fun (b : β) => _inst_3 b))) (Set.pi.{u1, u2} β (fun (b : β) => π b) (Set.univ.{u1} β) s)))
but is expected to have type
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoEMetricSpace.{u2} (π b)] {s : forall (b : β), Set.{u2} (π b)} {c : ENNReal}, (forall (b : β), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) c (Set.einfsep.{u2} (π b) (PseudoEMetricSpace.toEDist.{u2} (π b) (_inst_3 b)) (s b))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) c (Set.einfsep.{max u2 u1} (forall (i : β), π i) (instEDistForAll.{u1, u2} β (fun (i : β) => π i) _inst_2 (fun (b : β) => PseudoEMetricSpace.toEDist.{u2} (π b) (_inst_3 b))) (Set.pi.{u1, u2} β (fun (b : β) => π b) (Set.univ.{u1} β) s)))
Case conversion may be inaccurate. Consider using '#align set.le_einfsep_pi_of_le Set.le_einfsep_pi_of_leₓ'. -/
theorem le_einfsep_pi_of_le {π : β → Type _} [Fintype β] [∀ b, PseudoEMetricSpace (π b)]
    {s : ∀ b : β, Set (π b)} {c : ℝ≥0∞} (h : ∀ b, c ≤ einfsep (s b)) :
    c ≤ einfsep (Set.pi univ s) :=
  by
  refine' le_einfsep fun x hx y hy hxy => _
  rw [mem_univ_pi] at hx hy
  rcases function.ne_iff.mp hxy with ⟨i, hi⟩
  exact le_trans (le_einfsep_iff.1 (h i) _ (hx _) _ (hy _) hi) (edist_le_pi_edist _ _ i)
#align set.le_einfsep_pi_of_le Set.le_einfsep_pi_of_le

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {s : Set α}

/- warning: set.subsingleton_of_einfsep_eq_top -> Set.subsingleton_of_einfsep_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Eq.{1} ENNReal (Set.einfsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Set.Subsingleton.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Eq.{1} ENNReal (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Set.Subsingleton.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.subsingleton_of_einfsep_eq_top Set.subsingleton_of_einfsep_eq_topₓ'. -/
theorem subsingleton_of_einfsep_eq_top (hs : s.einfsep = ∞) : s.Subsingleton :=
  by
  rw [einfsep_top] at hs
  exact fun _ hx _ hy => of_not_not fun hxy => edist_ne_top _ _ (hs _ hx _ hy hxy)
#align set.subsingleton_of_einfsep_eq_top Set.subsingleton_of_einfsep_eq_top

/- warning: set.einfsep_eq_top_iff -> Set.einfsep_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Eq.{1} ENNReal (Set.einfsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Set.Subsingleton.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Eq.{1} ENNReal (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.Subsingleton.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.einfsep_eq_top_iff Set.einfsep_eq_top_iffₓ'. -/
theorem einfsep_eq_top_iff : s.einfsep = ∞ ↔ s.Subsingleton :=
  ⟨subsingleton_of_einfsep_eq_top, Subsingleton.einfsep⟩
#align set.einfsep_eq_top_iff Set.einfsep_eq_top_iff

/- warning: set.nontrivial.einfsep_ne_top -> Set.Nontrivial.einfsep_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (Ne.{1} ENNReal (Set.einfsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (Ne.{1} ENNReal (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align set.nontrivial.einfsep_ne_top Set.Nontrivial.einfsep_ne_topₓ'. -/
theorem Nontrivial.einfsep_ne_top (hs : s.Nontrivial) : s.einfsep ≠ ∞ :=
  by
  contrapose! hs
  rw [not_nontrivial_iff]
  exact subsingleton_of_einfsep_eq_top hs
#align set.nontrivial.einfsep_ne_top Set.Nontrivial.einfsep_ne_top

/- warning: set.nontrivial.einfsep_lt_top -> Set.Nontrivial.einfsep_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align set.nontrivial.einfsep_lt_top Set.Nontrivial.einfsep_lt_topₓ'. -/
theorem Nontrivial.einfsep_lt_top (hs : s.Nontrivial) : s.einfsep < ∞ :=
  by
  rw [lt_top_iff_ne_top]
  exact hs.einfsep_ne_top
#align set.nontrivial.einfsep_lt_top Set.Nontrivial.einfsep_lt_top

/- warning: set.einfsep_lt_top_iff -> Set.einfsep_lt_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Set.Nontrivial.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.Nontrivial.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.einfsep_lt_top_iff Set.einfsep_lt_top_iffₓ'. -/
theorem einfsep_lt_top_iff : s.einfsep < ∞ ↔ s.Nontrivial :=
  ⟨nontrivial_of_einfsep_lt_top, Nontrivial.einfsep_lt_top⟩
#align set.einfsep_lt_top_iff Set.einfsep_lt_top_iff

/- warning: set.einfsep_ne_top_iff -> Set.einfsep_ne_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Ne.{1} ENNReal (Set.einfsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Set.Nontrivial.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Ne.{1} ENNReal (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.Nontrivial.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.einfsep_ne_top_iff Set.einfsep_ne_top_iffₓ'. -/
theorem einfsep_ne_top_iff : s.einfsep ≠ ∞ ↔ s.Nontrivial :=
  ⟨nontrivial_of_einfsep_ne_top, Nontrivial.einfsep_ne_top⟩
#align set.einfsep_ne_top_iff Set.einfsep_ne_top_iff

/- warning: set.le_einfsep_of_forall_dist_le -> Set.le_einfsep_of_forall_dist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.hasLe d (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (ENNReal.ofReal d) (Set.einfsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.instLEReal d (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENNReal.ofReal d) (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align set.le_einfsep_of_forall_dist_le Set.le_einfsep_of_forall_dist_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem le_einfsep_of_forall_dist_le {d}
    (h : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s) (hxy : x ≠ y), d ≤ dist x y) :
    ENNReal.ofReal d ≤ s.einfsep :=
  le_einfsep fun x hx y hy hxy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy hxy)
#align set.le_einfsep_of_forall_dist_le Set.le_einfsep_of_forall_dist_le

end PseudoMetricSpace

section EMetricSpace

variable [EMetricSpace α] {x y z : α} {s t : Set α} {C : ℝ≥0∞} {sC : Set ℝ≥0∞}

/- warning: set.einfsep_pos_of_finite -> Set.einfsep_pos_of_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)], LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (Set.einfsep.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_1)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Finite.{succ u1} (Set.Elem.{u1} α s)], LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s)
Case conversion may be inaccurate. Consider using '#align set.einfsep_pos_of_finite Set.einfsep_pos_of_finiteₓ'. -/
theorem einfsep_pos_of_finite [Finite s] : 0 < s.einfsep :=
  by
  cases nonempty_fintype s
  by_cases hs : s.nontrivial
  · rcases hs.einfsep_exists_of_finite with ⟨x, hx, y, hy, hxy, hxy'⟩
    exact hxy'.symm ▸ edist_pos.2 hxy
  · rw [not_nontrivial_iff] at hs
    exact hs.einfsep.symm ▸ WithTop.zero_lt_top
#align set.einfsep_pos_of_finite Set.einfsep_pos_of_finite

/- warning: set.relatively_discrete_of_finite -> Set.relatively_discrete_of_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)], Exists.{1} ENNReal (fun (C : ENNReal) => Exists.{0} (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) C) (fun (hC : LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) C) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) C (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_1)) x y)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Finite.{succ u1} (Set.Elem.{u1} α s)], Exists.{1} ENNReal (fun (C : ENNReal) => Exists.{0} (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) C) (fun (hC : LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) C) => forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) C (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) x y)))))
Case conversion may be inaccurate. Consider using '#align set.relatively_discrete_of_finite Set.relatively_discrete_of_finiteₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem relatively_discrete_of_finite [Finite s] :
    ∃ (C : _)(hC : 0 < C), ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s) (hxy : x ≠ y), C ≤ edist x y :=
  by
  rw [← einfsep_pos]
  exact einfsep_pos_of_finite
#align set.relatively_discrete_of_finite Set.relatively_discrete_of_finite

/- warning: set.finite.einfsep_pos -> Set.Finite.einfsep_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (Set.einfsep.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (Set.einfsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align set.finite.einfsep_pos Set.Finite.einfsep_posₓ'. -/
theorem Finite.einfsep_pos (hs : s.Finite) : 0 < s.einfsep :=
  letI := hs.fintype
  einfsep_pos_of_finite
#align set.finite.einfsep_pos Set.Finite.einfsep_pos

/- warning: set.finite.relatively_discrete -> Set.Finite.relatively_discrete is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Exists.{1} ENNReal (fun (C : ENNReal) => Exists.{0} (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) C) (fun (hC : LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) C) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) C (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_1)) x y))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Exists.{1} ENNReal (fun (C : ENNReal) => Exists.{0} (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) C) (fun (hC : LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) C) => forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) C (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) x y))))))
Case conversion may be inaccurate. Consider using '#align set.finite.relatively_discrete Set.Finite.relatively_discreteₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem Finite.relatively_discrete (hs : s.Finite) :
    ∃ (C : _)(hC : 0 < C), ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s) (hxy : x ≠ y), C ≤ edist x y :=
  letI := hs.fintype
  relatively_discrete_of_finite
#align set.finite.relatively_discrete Set.Finite.relatively_discrete

end EMetricSpace

end Einfsep

section Infsep

open ENNReal

open Set Function

#print Set.infsep /-
/-- The "infimum separation" of a set with an edist function. -/
noncomputable def infsep [EDist α] (s : Set α) : ℝ :=
  ENNReal.toReal s.einfsep
#align set.infsep Set.infsep
-/

section EDist

variable [EDist α] {x y : α} {s : Set α}

/- warning: set.infsep_zero -> Set.infsep_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (Eq.{1} Real (Set.infsep.{u1} α _inst_1 s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Or (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (Eq.{1} Real (Set.infsep.{u1} α _inst_1 s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Or (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{1} ENNReal (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align set.infsep_zero Set.infsep_zeroₓ'. -/
theorem infsep_zero : s.infsep = 0 ↔ s.einfsep = 0 ∨ s.einfsep = ∞ := by
  rw [infsep, ENNReal.toReal_eq_zero_iff]
#align set.infsep_zero Set.infsep_zero

/- warning: set.infsep_nonneg -> Set.infsep_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.infsep.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.infsep.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align set.infsep_nonneg Set.infsep_nonnegₓ'. -/
theorem infsep_nonneg : 0 ≤ s.infsep :=
  ENNReal.toReal_nonneg
#align set.infsep_nonneg Set.infsep_nonneg

/- warning: set.infsep_pos -> Set.infsep_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.infsep.{u1} α _inst_1 s)) (And (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (Set.einfsep.{u1} α _inst_1 s)) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.infsep.{u1} α _inst_1 s)) (And (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (Set.einfsep.{u1} α _inst_1 s)) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Set.einfsep.{u1} α _inst_1 s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align set.infsep_pos Set.infsep_posₓ'. -/
theorem infsep_pos : 0 < s.infsep ↔ 0 < s.einfsep ∧ s.einfsep < ∞ := by
  simp_rw [infsep, ENNReal.toReal_pos_iff]
#align set.infsep_pos Set.infsep_pos

/- warning: set.subsingleton.infsep_zero -> Set.Subsingleton.infsep_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (Eq.{1} Real (Set.infsep.{u1} α _inst_1 s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (Eq.{1} Real (Set.infsep.{u1} α _inst_1 s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align set.subsingleton.infsep_zero Set.Subsingleton.infsep_zeroₓ'. -/
theorem Subsingleton.infsep_zero (hs : s.Subsingleton) : s.infsep = 0 :=
  by
  rw [infsep_zero, hs.einfsep]
  right
  rfl
#align set.subsingleton.infsep_zero Set.Subsingleton.infsep_zero

/- warning: set.nontrivial_of_infsep_pos -> Set.nontrivial_of_infsep_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.infsep.{u1} α _inst_1 s)) -> (Set.Nontrivial.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {s : Set.{u1} α}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.infsep.{u1} α _inst_1 s)) -> (Set.Nontrivial.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.nontrivial_of_infsep_pos Set.nontrivial_of_infsep_posₓ'. -/
theorem nontrivial_of_infsep_pos (hs : 0 < s.infsep) : s.Nontrivial :=
  by
  contrapose hs
  rw [not_nontrivial_iff] at hs
  exact hs.infsep_zero ▸ lt_irrefl _
#align set.nontrivial_of_infsep_pos Set.nontrivial_of_infsep_pos

/- warning: set.infsep_empty -> Set.infsep_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α], Eq.{1} Real (Set.infsep.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α], Eq.{1} Real (Set.infsep.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align set.infsep_empty Set.infsep_emptyₓ'. -/
theorem infsep_empty : (∅ : Set α).infsep = 0 :=
  subsingleton_empty.infsep_zero
#align set.infsep_empty Set.infsep_empty

/- warning: set.infsep_singleton -> Set.infsep_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α}, Eq.{1} Real (Set.infsep.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α}, Eq.{1} Real (Set.infsep.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align set.infsep_singleton Set.infsep_singletonₓ'. -/
theorem infsep_singleton : ({x} : Set α).infsep = 0 :=
  subsingleton_singleton.infsep_zero
#align set.infsep_singleton Set.infsep_singleton

/- warning: set.infsep_pair_le_to_real_inf -> Set.infsep_pair_le_toReal_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {y : α}, (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.hasLe (Set.infsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) y))) (ENNReal.toReal (Inf.inf.{0} ENNReal (SemilatticeInf.toHasInf.{0} ENNReal (Lattice.toSemilatticeInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α _inst_1 x y) (EDist.edist.{u1} α _inst_1 y x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : EDist.{u1} α] {x : α} {y : α}, (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.instLEReal (Set.infsep.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) y))) (ENNReal.toReal (Inf.inf.{0} ENNReal (Lattice.toInf.{0} ENNReal (ConditionallyCompleteLattice.toLattice.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α _inst_1 x y) (EDist.edist.{u1} α _inst_1 y x))))
Case conversion may be inaccurate. Consider using '#align set.infsep_pair_le_to_real_inf Set.infsep_pair_le_toReal_infₓ'. -/
theorem infsep_pair_le_toReal_inf (hxy : x ≠ y) :
    ({x, y} : Set α).infsep ≤ (edist x y ⊓ edist y x).toReal := by
  simp_rw [infsep, einfsep_pair_eq_inf hxy]
#align set.infsep_pair_le_to_real_inf Set.infsep_pair_le_toReal_inf

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y : α} {s : Set α}

#print Set.infsep_pair_eq_toReal /-
theorem infsep_pair_eq_toReal : ({x, y} : Set α).infsep = (edist x y).toReal :=
  by
  by_cases hxy : x = y
  · rw [hxy]
    simp only [infsep_singleton, pair_eq_singleton, edist_self, ENNReal.zero_toReal]
  · rw [infsep, einfsep_pair hxy]
#align set.infsep_pair_eq_to_real Set.infsep_pair_eq_toReal
-/

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {x y z : α} {s t : Set α}

/- warning: set.nontrivial.le_infsep_iff -> Set.Nontrivial.le_infsep_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real}, (Set.Nontrivial.{u1} α s) -> (Iff (LE.le.{0} Real Real.hasLe d (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s)) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.hasLe d (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real}, (Set.Nontrivial.{u1} α s) -> (Iff (LE.le.{0} Real Real.instLEReal d (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s)) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.instLEReal d (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)))))
Case conversion may be inaccurate. Consider using '#align set.nontrivial.le_infsep_iff Set.Nontrivial.le_infsep_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem Nontrivial.le_infsep_iff {d} (hs : s.Nontrivial) :
    d ≤ s.infsep ↔ ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s) (hxy : x ≠ y), d ≤ dist x y := by
  simp_rw [infsep, ← ENNReal.ofReal_le_iff_le_toReal hs.einfsep_ne_top, le_einfsep_iff, edist_dist,
    ENNReal.ofReal_le_ofReal_iff dist_nonneg]
#align set.nontrivial.le_infsep_iff Set.Nontrivial.le_infsep_iff

/- warning: set.nontrivial.infsep_lt_iff -> Set.Nontrivial.infsep_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real}, (Set.Nontrivial.{u1} α s) -> (Iff (LT.lt.{0} Real Real.hasLt (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) d) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => Exists.{0} (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) d)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real}, (Set.Nontrivial.{u1} α s) -> (Iff (LT.lt.{0} Real Real.instLTReal (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) d) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) => Exists.{0} (Ne.{succ u1} α x y) (fun (hxy : Ne.{succ u1} α x y) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) d)))))))
Case conversion may be inaccurate. Consider using '#align set.nontrivial.infsep_lt_iff Set.Nontrivial.infsep_lt_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem Nontrivial.infsep_lt_iff {d} (hs : s.Nontrivial) :
    s.infsep < d ↔ ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s)(hxy : x ≠ y), dist x y < d :=
  by
  rw [← not_iff_not]
  push_neg
  exact hs.le_infsep_iff
#align set.nontrivial.infsep_lt_iff Set.Nontrivial.infsep_lt_iff

/- warning: set.nontrivial.le_infsep -> Set.Nontrivial.le_infsep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real}, (Set.Nontrivial.{u1} α s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.hasLe d (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)))) -> (LE.le.{0} Real Real.hasLe d (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real}, (Set.Nontrivial.{u1} α s) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.instLEReal d (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)))) -> (LE.le.{0} Real Real.instLEReal d (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align set.nontrivial.le_infsep Set.Nontrivial.le_infsepₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem Nontrivial.le_infsep {d} (hs : s.Nontrivial)
    (h : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s) (hxy : x ≠ y), d ≤ dist x y) : d ≤ s.infsep :=
  hs.le_infsep_iff.2 h
#align set.nontrivial.le_infsep Set.Nontrivial.le_infsep

/- warning: set.le_edist_of_le_infsep -> Set.le_edist_of_le_infsep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall {y : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.hasLe d (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s)) -> (LE.le.{0} Real Real.hasLe d (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall {y : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.instLEReal d (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s)) -> (LE.le.{0} Real Real.instLEReal d (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)))
Case conversion may be inaccurate. Consider using '#align set.le_edist_of_le_infsep Set.le_edist_of_le_infsepₓ'. -/
theorem le_edist_of_le_infsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ s.infsep) : d ≤ dist x y :=
  by
  by_cases hs : s.nontrivial
  · exact hs.le_infsep_iff.1 hd x hx y hy hxy
  · rw [not_nontrivial_iff] at hs
    rw [hs.infsep_zero] at hd
    exact le_trans hd dist_nonneg
#align set.le_edist_of_le_infsep Set.le_edist_of_le_infsep

/- warning: set.infsep_le_dist_of_mem -> Set.infsep_le_dist_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.hasLe (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.instLEReal (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y))
Case conversion may be inaccurate. Consider using '#align set.infsep_le_dist_of_mem Set.infsep_le_dist_of_memₓ'. -/
theorem infsep_le_dist_of_mem (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.infsep ≤ dist x y :=
  le_edist_of_le_infsep hx hy hxy le_rfl
#align set.infsep_le_dist_of_mem Set.infsep_le_dist_of_mem

/- warning: set.infsep_le_of_mem_of_edist_le -> Set.infsep_le_of_mem_of_edist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall {y : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) d) -> (LE.le.{0} Real Real.hasLe (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {d : Real} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall {y : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (Ne.{succ u1} α x y) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) d) -> (LE.le.{0} Real Real.instLEReal (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) d))
Case conversion may be inaccurate. Consider using '#align set.infsep_le_of_mem_of_edist_le Set.infsep_le_of_mem_of_edist_leₓ'. -/
theorem infsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : dist x y ≤ d) : s.infsep ≤ d :=
  le_trans (infsep_le_dist_of_mem hx hy hxy) hxy'
#align set.infsep_le_of_mem_of_edist_le Set.infsep_le_of_mem_of_edist_le

#print Set.infsep_pair /-
theorem infsep_pair : ({x, y} : Set α).infsep = dist x y :=
  by
  rw [infsep_pair_eq_to_real, edist_dist]
  exact ENNReal.toReal_ofReal dist_nonneg
#align set.infsep_pair Set.infsep_pair
-/

/- warning: set.infsep_triple -> Set.infsep_triple is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {z : α}, (Ne.{succ u1} α x y) -> (Ne.{succ u1} α y z) -> (Ne.{succ u1} α x z) -> (Eq.{1} Real (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) y (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) z)))) (Inf.inf.{0} Real Real.hasInf (Inf.inf.{0} Real Real.hasInf (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x z)) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y z)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {z : α}, (Ne.{succ u1} α x y) -> (Ne.{succ u1} α y z) -> (Ne.{succ u1} α x z) -> (Eq.{1} Real (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) y (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) z)))) (Inf.inf.{0} Real Real.instInfReal (Inf.inf.{0} Real Real.instInfReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x z)) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y z)))
Case conversion may be inaccurate. Consider using '#align set.infsep_triple Set.infsep_tripleₓ'. -/
theorem infsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ({x, y, z} : Set α).infsep = dist x y ⊓ dist x z ⊓ dist y z := by
  simp only [infsep, einfsep_triple hxy hyz hxz, ENNReal.toReal_inf, edist_ne_top x y,
    edist_ne_top x z, edist_ne_top y z, dist_edist, Ne.def, inf_eq_top_iff, and_self_iff,
    not_false_iff]
#align set.infsep_triple Set.infsep_triple

/- warning: set.nontrivial.infsep_anti -> Set.Nontrivial.infsep_anti is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{0} Real Real.hasLe (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) t) (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{0} Real Real.instLEReal (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) t) (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align set.nontrivial.infsep_anti Set.Nontrivial.infsep_antiₓ'. -/
theorem Nontrivial.infsep_anti (hs : s.Nontrivial) (hst : s ⊆ t) : t.infsep ≤ s.infsep :=
  ENNReal.toReal_mono hs.einfsep_ne_top (einfsep_anti hst)
#align set.nontrivial.infsep_anti Set.Nontrivial.infsep_anti

/- warning: set.infsep_eq_infi -> Set.infsep_eq_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Decidable (Set.Nontrivial.{u1} α s)], Eq.{1} Real (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) (ite.{1} Real (Set.Nontrivial.{u1} α s) _inst_2 (iInf.{0, succ u1} Real Real.hasInf (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (fun (d : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) => Function.uncurry.{u1, u1, 0} α α Real (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (coeSubtype.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) x (Set.offDiag.{u1} α s)))))) d))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Decidable (Set.Nontrivial.{u1} α s)], Eq.{1} Real (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) (ite.{1} Real (Set.Nontrivial.{u1} α s) _inst_2 (iInf.{0, succ u1} Real Real.instInfSetReal (Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) (fun (d : Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) => Function.uncurry.{u1, u1, 0} α α Real (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1)) (Subtype.val.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) x (Set.offDiag.{u1} α s)) d))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align set.infsep_eq_infi Set.infsep_eq_iInfₓ'. -/
theorem infsep_eq_iInf [Decidable s.Nontrivial] :
    s.infsep = if s.Nontrivial then ⨅ d : s.offDiag, (uncurry dist) (d : α × α) else 0 :=
  by
  split_ifs with hs
  · have hb : BddBelow (uncurry dist '' s.off_diag) :=
      by
      refine' ⟨0, fun d h => _⟩
      simp_rw [mem_image, Prod.exists, uncurry_apply_pair] at h
      rcases h with ⟨_, _, _, rfl⟩
      exact dist_nonneg
    refine' eq_of_forall_le_iff fun _ => _
    simp_rw [hs.le_infsep_iff, le_ciInf_set_iff (off_diag_nonempty.mpr hs) hb, imp_forall_iff,
      mem_off_diag, Prod.forall, uncurry_apply_pair, and_imp]
  · exact (not_nontrivial_iff.mp hs).infsep_zero
#align set.infsep_eq_infi Set.infsep_eq_iInf

/- warning: set.nontrivial.infsep_eq_infi -> Set.Nontrivial.infsep_eq_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (Eq.{1} Real (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) (iInf.{0, succ u1} Real Real.hasInf (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (fun (d : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) => Function.uncurry.{u1, u1, 0} α α Real (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α α)) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s)) (Prod.{u1, u1} α α) (coeSubtype.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) x (Set.offDiag.{u1} α s)))))) d))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (Eq.{1} Real (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) (iInf.{0, succ u1} Real Real.instInfSetReal (Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) (fun (d : Set.Elem.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) => Function.uncurry.{u1, u1, 0} α α Real (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1)) (Subtype.val.{succ u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) x (Set.offDiag.{u1} α s)) d))))
Case conversion may be inaccurate. Consider using '#align set.nontrivial.infsep_eq_infi Set.Nontrivial.infsep_eq_iInfₓ'. -/
theorem Nontrivial.infsep_eq_iInf (hs : s.Nontrivial) :
    s.infsep = ⨅ d : s.offDiag, (uncurry dist) (d : α × α) := by
  classical rw [infsep_eq_infi, if_pos hs]
#align set.nontrivial.infsep_eq_infi Set.Nontrivial.infsep_eq_iInf

/- warning: set.infsep_of_fintype -> Set.infsep_of_fintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Decidable (Set.Nontrivial.{u1} α s)] [_inst_3 : DecidableEq.{succ u1} α] [_inst_4 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)], Eq.{1} Real (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) (dite.{1} Real (Set.Nontrivial.{u1} α s) _inst_2 (fun (hs : Set.Nontrivial.{u1} α s) => Finset.inf'.{0, u1} Real (Prod.{u1, u1} α α) Real.semilatticeInf (Set.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _inst_4)) (Eq.mpr.{0} (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _inst_4))) (Set.Nontrivial.{u1} α s) (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _inst_4))) (Set.Nontrivial.{u1} α s)) (Eq.trans.{1} Prop (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _inst_4))) (Set.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) (Set.Nontrivial.{u1} α s) (propext (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _inst_4))) (Set.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) (Set.toFinset_nonempty.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _inst_4))) (propext (Set.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) (Set.Nontrivial.{u1} α s) (Set.offDiag_nonempty.{u1} α s)))) hs) (Function.uncurry.{u1, u1, 0} α α Real (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1)))) (fun (hs : Not (Set.Nontrivial.{u1} α s)) => OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Decidable (Set.Nontrivial.{u1} α s)] [_inst_3 : DecidableEq.{succ u1} α] [_inst_4 : Fintype.{u1} (Set.Elem.{u1} α s)], Eq.{1} Real (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) (dite.{1} Real (Set.Nontrivial.{u1} α s) _inst_2 (fun (hs : Set.Nontrivial.{u1} α s) => Finset.inf'.{0, u1} Real (Prod.{u1, u1} α α) Real.instSemilatticeInfReal (Set.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _inst_4)) (Eq.mpr.{0} (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _inst_4))) (Set.Nontrivial.{u1} α s) (id.{0} (Eq.{1} Prop (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _inst_4))) (Set.Nontrivial.{u1} α s)) (Eq.trans.{1} Prop (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _inst_4))) (Set.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) (Set.Nontrivial.{u1} α s) (Mathlib.Data.Fintype.Basic._auxLemma.20.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.fintypeOffDiag.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _inst_4)) (Mathlib.Data.Set.Prod._auxLemma.33.{u1} α s))) hs) (Function.uncurry.{u1, u1, 0} α α Real (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1)))) (fun (hs : Not (Set.Nontrivial.{u1} α s)) => OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align set.infsep_of_fintype Set.infsep_of_fintypeₓ'. -/
theorem infsep_of_fintype [Decidable s.Nontrivial] [DecidableEq α] [Fintype s] :
    s.infsep = if hs : s.Nontrivial then s.offDiag.toFinset.inf' (by simpa) (uncurry dist) else 0 :=
  by
  split_ifs with hs
  · refine' eq_of_forall_le_iff fun _ => _
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, mem_to_finset, mem_off_diag,
      Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero
#align set.infsep_of_fintype Set.infsep_of_fintype

#print Set.Nontrivial.infsep_of_fintype /-
theorem Nontrivial.infsep_of_fintype [DecidableEq α] [Fintype s] (hs : s.Nontrivial) :
    s.infsep = s.offDiag.toFinset.inf' (by simpa) (uncurry dist) := by
  classical rw [infsep_of_fintype, dif_pos hs]
#align set.nontrivial.infsep_of_fintype Set.Nontrivial.infsep_of_fintype
-/

/- warning: set.finite.infsep -> Set.Finite.infsep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Decidable (Set.Nontrivial.{u1} α s)] (hsf : Set.Finite.{u1} α s), Eq.{1} Real (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) s) (dite.{1} Real (Set.Nontrivial.{u1} α s) _inst_2 (fun (hs : Set.Nontrivial.{u1} α s) => Finset.inf'.{0, u1} Real (Prod.{u1, u1} α α) Real.semilatticeInf (Set.Finite.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hsf)) (Eq.mpr.{0} (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.Finite.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hsf))) (Set.Nontrivial.{u1} α s) (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.Finite.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hsf))) (Set.Nontrivial.{u1} α s)) (Eq.trans.{1} Prop (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.Finite.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hsf))) (Set.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) (Set.Nontrivial.{u1} α s) (propext (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.Finite.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hsf))) (Set.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) (Set.Finite.toFinset_nonempty.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hsf))) (propext (Set.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) (Set.Nontrivial.{u1} α s) (Set.offDiag_nonempty.{u1} α s)))) hs) (Function.uncurry.{u1, u1, 0} α α Real (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1)))) (fun (hs : Not (Set.Nontrivial.{u1} α s)) => OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Decidable (Set.Nontrivial.{u1} α s)] (hsf : Set.Finite.{u1} α s), Eq.{1} Real (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) s) (dite.{1} Real (Set.Nontrivial.{u1} α s) _inst_2 (fun (hs : Set.Nontrivial.{u1} α s) => Finset.inf'.{0, u1} Real (Prod.{u1, u1} α α) Real.instSemilatticeInfReal (Set.Finite.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hsf)) (Eq.mpr.{0} (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.Finite.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hsf))) (Set.Nontrivial.{u1} α s) (id.{0} (Eq.{1} Prop (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.Finite.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hsf))) (Set.Nontrivial.{u1} α s)) (Eq.trans.{1} Prop (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.Finite.toFinset.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hsf))) (Set.Nonempty.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s)) (Set.Nontrivial.{u1} α s) (Mathlib.Data.Set.Finite._auxLemma.4.{u1} (Prod.{u1, u1} α α) (Set.offDiag.{u1} α s) (Set.Finite.offDiag.{u1} α s hsf)) (Mathlib.Data.Set.Prod._auxLemma.33.{u1} α s))) hs) (Function.uncurry.{u1, u1, 0} α α Real (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1)))) (fun (hs : Not (Set.Nontrivial.{u1} α s)) => OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align set.finite.infsep Set.Finite.infsepₓ'. -/
theorem Finite.infsep [Decidable s.Nontrivial] (hsf : s.Finite) :
    s.infsep =
      if hs : s.Nontrivial then hsf.offDiag.toFinset.inf' (by simpa) (uncurry dist) else 0 :=
  by
  split_ifs with hs
  · refine' eq_of_forall_le_iff fun _ => _
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, finite.mem_to_finset,
      mem_off_diag, Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero
#align set.finite.infsep Set.Finite.infsep

#print Set.Finite.infsep_of_nontrivial /-
theorem Finite.infsep_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    s.infsep = hsf.offDiag.toFinset.inf' (by simpa) (uncurry dist) := by
  classical simp_rw [hsf.infsep, dif_pos hs]
#align set.finite.infsep_of_nontrivial Set.Finite.infsep_of_nontrivial
-/

/- warning: finset.coe_infsep -> Finset.coe_infsep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{1} Real (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (dite.{1} Real (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s)) (Finset.decidableNonempty.{u1} (Prod.{u1, u1} α α) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s)) (fun (hs : Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s)) => Finset.inf'.{0, u1} Real (Prod.{u1, u1} α α) Real.semilatticeInf (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s) hs (Function.uncurry.{u1, u1, 0} α α Real (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1)))) (fun (hs : Not (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s))) => OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{1} Real (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) (Finset.toSet.{u1} α s)) (dite.{1} Real (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s)) (Finset.decidableNonempty.{u1} (Prod.{u1, u1} α α) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s)) (fun (hs : Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s)) => Finset.inf'.{0, u1} Real (Prod.{u1, u1} α α) Real.instSemilatticeInfReal (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s) hs (Function.uncurry.{u1, u1, 0} α α Real (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1)))) (fun (hs : Not (Finset.Nonempty.{u1} (Prod.{u1, u1} α α) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s))) => OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align finset.coe_infsep Finset.coe_infsepₓ'. -/
theorem Finset.coe_infsep [DecidableEq α] (s : Finset α) :
    (s : Set α).infsep = if hs : s.offDiag.Nonempty then s.offDiag.inf' hs (uncurry dist) else 0 :=
  by
  have H : (s : Set α).Nontrivial ↔ s.off_diag.nonempty := by
    rwa [← Set.offDiag_nonempty, ← Finset.coe_offDiag, Finset.coe_nonempty]
  split_ifs with hs
  · simp_rw [(H.mpr hs).infsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]
  · exact (not_nontrivial_iff.mp (H.mp.mt hs)).infsep_zero
#align finset.coe_infsep Finset.coe_infsep

#print Finset.coe_infsep_of_offDiag_nonempty /-
theorem Finset.coe_infsep_of_offDiag_nonempty [DecidableEq α] {s : Finset α}
    (hs : s.offDiag.Nonempty) : (s : Set α).infsep = s.offDiag.inf' hs (uncurry dist) := by
  rw [Finset.coe_infsep, dif_pos hs]
#align finset.coe_infsep_of_off_diag_nonempty Finset.coe_infsep_of_offDiag_nonempty
-/

/- warning: finset.coe_infsep_of_off_diag_empty -> Finset.coe_infsep_of_offDiag_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, (Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasEmptyc.{u1} (Prod.{u1, u1} α α)))) -> (Eq.{1} Real (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, (Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instEmptyCollectionFinset.{u1} (Prod.{u1, u1} α α)))) -> (Eq.{1} Real (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) (Finset.toSet.{u1} α s)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align finset.coe_infsep_of_off_diag_empty Finset.coe_infsep_of_offDiag_emptyₓ'. -/
theorem Finset.coe_infsep_of_offDiag_empty [DecidableEq α] {s : Finset α} (hs : s.offDiag = ∅) :
    (s : Set α).infsep = 0 :=
  by
  rw [← Finset.not_nonempty_iff_eq_empty] at hs
  rw [Finset.coe_infsep, dif_neg hs]
#align finset.coe_infsep_of_off_diag_empty Finset.coe_infsep_of_offDiag_empty

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
#print Set.Nontrivial.infsep_exists_of_finite /-
theorem Nontrivial.infsep_exists_of_finite [Finite s] (hs : s.Nontrivial) :
    ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s)(hxy : x ≠ y), s.infsep = dist x y := by
  classical
    cases nonempty_fintype s
    simp_rw [hs.infsep_of_fintype]
    rcases@Finset.exists_mem_eq_inf' _ _ _ s.off_diag.to_finset (by simpa) (uncurry dist) with
      ⟨_, hxy, hed⟩
    simp_rw [mem_to_finset] at hxy
    exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩
#align set.nontrivial.infsep_exists_of_finite Set.Nontrivial.infsep_exists_of_finite
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
#print Set.Finite.infsep_exists_of_nontrivial /-
theorem Finite.infsep_exists_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s)(hxy : x ≠ y), s.infsep = dist x y :=
  letI := hsf.fintype
  hs.infsep_exists_of_finite
#align set.finite.infsep_exists_of_nontrivial Set.Finite.infsep_exists_of_nontrivial
-/

end PseudoMetricSpace

section MetricSpace

variable [MetricSpace α] {s : Set α}

/- warning: set.infsep_zero_iff_subsingleton_of_finite -> Set.infsep_zero_iff_subsingleton_of_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)], Iff (Eq.{1} Real (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)) s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Set.Subsingleton.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Finite.{succ u1} (Set.Elem.{u1} α s)], Iff (Eq.{1} Real (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toEMetricSpace.{u1} α _inst_1))) s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Set.Subsingleton.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.infsep_zero_iff_subsingleton_of_finite Set.infsep_zero_iff_subsingleton_of_finiteₓ'. -/
theorem infsep_zero_iff_subsingleton_of_finite [Finite s] : s.infsep = 0 ↔ s.Subsingleton :=
  by
  rw [infsep_zero, einfsep_eq_top_iff, or_iff_right_iff_imp]
  exact fun H => (einfsep_pos_of_finite.ne' H).elim
#align set.infsep_zero_iff_subsingleton_of_finite Set.infsep_zero_iff_subsingleton_of_finite

/- warning: set.infsep_pos_iff_nontrivial_of_finite -> Set.infsep_pos_iff_nontrivial_of_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)], Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)) s)) (Set.Nontrivial.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : Finite.{succ u1} (Set.Elem.{u1} α s)], Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toEMetricSpace.{u1} α _inst_1))) s)) (Set.Nontrivial.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.infsep_pos_iff_nontrivial_of_finite Set.infsep_pos_iff_nontrivial_of_finiteₓ'. -/
theorem infsep_pos_iff_nontrivial_of_finite [Finite s] : 0 < s.infsep ↔ s.Nontrivial :=
  by
  rw [infsep_pos, einfsep_lt_top_iff, and_iff_right_iff_imp]
  exact fun _ => einfsep_pos_of_finite
#align set.infsep_pos_iff_nontrivial_of_finite Set.infsep_pos_iff_nontrivial_of_finite

/- warning: set.finite.infsep_zero_iff_subsingleton -> Set.Finite.infsep_zero_iff_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Iff (Eq.{1} Real (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)) s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Set.Subsingleton.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Iff (Eq.{1} Real (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toEMetricSpace.{u1} α _inst_1))) s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Set.Subsingleton.{u1} α s))
Case conversion may be inaccurate. Consider using '#align set.finite.infsep_zero_iff_subsingleton Set.Finite.infsep_zero_iff_subsingletonₓ'. -/
theorem Finite.infsep_zero_iff_subsingleton (hs : s.Finite) : s.infsep = 0 ↔ s.Subsingleton :=
  letI := hs.fintype
  infsep_zero_iff_subsingleton_of_finite
#align set.finite.infsep_zero_iff_subsingleton Set.Finite.infsep_zero_iff_subsingleton

/- warning: set.finite.infsep_pos_iff_nontrivial -> Set.Finite.infsep_pos_iff_nontrivial is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)) s)) (Set.Nontrivial.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toEMetricSpace.{u1} α _inst_1))) s)) (Set.Nontrivial.{u1} α s))
Case conversion may be inaccurate. Consider using '#align set.finite.infsep_pos_iff_nontrivial Set.Finite.infsep_pos_iff_nontrivialₓ'. -/
theorem Finite.infsep_pos_iff_nontrivial (hs : s.Finite) : 0 < s.infsep ↔ s.Nontrivial :=
  letI := hs.fintype
  infsep_pos_iff_nontrivial_of_finite
#align set.finite.infsep_pos_iff_nontrivial Set.Finite.infsep_pos_iff_nontrivial

/- warning: finset.infsep_zero_iff_subsingleton -> Finset.infsep_zero_iff_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] (s : Finset.{u1} α), Iff (Eq.{1} Real (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Set.Subsingleton.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] (s : Finset.{u1} α), Iff (Eq.{1} Real (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toEMetricSpace.{u1} α _inst_1))) (Finset.toSet.{u1} α s)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Set.Subsingleton.{u1} α (Finset.toSet.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.infsep_zero_iff_subsingleton Finset.infsep_zero_iff_subsingletonₓ'. -/
theorem Finset.infsep_zero_iff_subsingleton (s : Finset α) :
    (s : Set α).infsep = 0 ↔ (s : Set α).Subsingleton :=
  infsep_zero_iff_subsingleton_of_finite
#align finset.infsep_zero_iff_subsingleton Finset.infsep_zero_iff_subsingleton

/- warning: finset.infsep_pos_iff_nontrivial -> Finset.infsep_pos_iff_nontrivial is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] (s : Finset.{u1} α), Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.infsep.{u1} α (PseudoMetricSpace.toEDist.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))) (Set.Nontrivial.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] (s : Finset.{u1} α), Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.infsep.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toEMetricSpace.{u1} α _inst_1))) (Finset.toSet.{u1} α s))) (Set.Nontrivial.{u1} α (Finset.toSet.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.infsep_pos_iff_nontrivial Finset.infsep_pos_iff_nontrivialₓ'. -/
theorem Finset.infsep_pos_iff_nontrivial (s : Finset α) :
    0 < (s : Set α).infsep ↔ (s : Set α).Nontrivial :=
  infsep_pos_iff_nontrivial_of_finite
#align finset.infsep_pos_iff_nontrivial Finset.infsep_pos_iff_nontrivial

end MetricSpace

end Infsep

end Set

