/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios

! This file was ported from Lean 3 source module order.bounded
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.RelClasses
import Mathbin.Data.Set.Intervals.Basic

/-!
# Bounded and unbounded sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove miscellaneous lemmas about bounded and unbounded sets. Many of these are just variations on
the same ideas, or similar results with a few minor differences. The file is divided into these
different general ideas.
-/


namespace Set

variable {α : Type _} {r : α → α → Prop} {s t : Set α}

/-! ### Subsets of bounded and unbounded sets -/


#print Set.Bounded.mono /-
theorem Bounded.mono (hst : s ⊆ t) (hs : Bounded r t) : Bounded r s :=
  hs.imp fun a ha b hb => ha b (hst hb)
#align set.bounded.mono Set.Bounded.mono
-/

#print Set.Unbounded.mono /-
theorem Unbounded.mono (hst : s ⊆ t) (hs : Unbounded r s) : Unbounded r t := fun a =>
  let ⟨b, hb, hb'⟩ := hs a
  ⟨b, hst hb, hb'⟩
#align set.unbounded.mono Set.Unbounded.mono
-/

/-! ### Alternate characterizations of unboundedness on orders -/


/- warning: set.unbounded_le_of_forall_exists_lt -> Set.unbounded_le_of_forall_exists_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α], (forall (a : α), Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b))) -> (Set.Unbounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α], (forall (a : α), Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b))) -> (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.172 : α) (x._@.Mathlib.Order.Bounded._hyg.174 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Bounded._hyg.172 x._@.Mathlib.Order.Bounded._hyg.174) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_le_of_forall_exists_lt Set.unbounded_le_of_forall_exists_ltₓ'. -/
theorem unbounded_le_of_forall_exists_lt [Preorder α] (h : ∀ a, ∃ b ∈ s, a < b) :
    Unbounded (· ≤ ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_lt hb'⟩
#align set.unbounded_le_of_forall_exists_lt Set.unbounded_le_of_forall_exists_lt

/- warning: set.unbounded_le_iff -> Set.unbounded_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α], Iff (Set.Unbounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s) (forall (a : α), Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α], Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.248 : α) (x._@.Mathlib.Order.Bounded._hyg.250 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.248 x._@.Mathlib.Order.Bounded._hyg.250) s) (forall (a : α), Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)))
Case conversion may be inaccurate. Consider using '#align set.unbounded_le_iff Set.unbounded_le_iffₓ'. -/
theorem unbounded_le_iff [LinearOrder α] : Unbounded (· ≤ ·) s ↔ ∀ a, ∃ b ∈ s, a < b := by
  simp only [unbounded, not_le]
#align set.unbounded_le_iff Set.unbounded_le_iff

/- warning: set.unbounded_lt_of_forall_exists_le -> Set.unbounded_lt_of_forall_exists_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α], (forall (a : α), Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b))) -> (Set.Unbounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1)) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α], (forall (a : α), Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b))) -> (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.336 : α) (x._@.Mathlib.Order.Bounded._hyg.338 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) x._@.Mathlib.Order.Bounded._hyg.336 x._@.Mathlib.Order.Bounded._hyg.338) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_lt_of_forall_exists_le Set.unbounded_lt_of_forall_exists_leₓ'. -/
theorem unbounded_lt_of_forall_exists_le [Preorder α] (h : ∀ a, ∃ b ∈ s, a ≤ b) :
    Unbounded (· < ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_le hb'⟩
#align set.unbounded_lt_of_forall_exists_le Set.unbounded_lt_of_forall_exists_le

/- warning: set.unbounded_lt_iff -> Set.unbounded_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α], Iff (Set.Unbounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s) (forall (a : α), Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α], Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.412 : α) (x._@.Mathlib.Order.Bounded._hyg.414 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.412 x._@.Mathlib.Order.Bounded._hyg.414) s) (forall (a : α), Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)))
Case conversion may be inaccurate. Consider using '#align set.unbounded_lt_iff Set.unbounded_lt_iffₓ'. -/
theorem unbounded_lt_iff [LinearOrder α] : Unbounded (· < ·) s ↔ ∀ a, ∃ b ∈ s, a ≤ b := by
  simp only [unbounded, not_lt]
#align set.unbounded_lt_iff Set.unbounded_lt_iff

/- warning: set.unbounded_ge_of_forall_exists_gt -> Set.unbounded_ge_of_forall_exists_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α], (forall (a : α), Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) b a))) -> (Set.Unbounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1)) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α], (forall (a : α), Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) b a))) -> (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.500 : α) (x._@.Mathlib.Order.Bounded._hyg.502 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Bounded._hyg.500 x._@.Mathlib.Order.Bounded._hyg.502) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_ge_of_forall_exists_gt Set.unbounded_ge_of_forall_exists_gtₓ'. -/
theorem unbounded_ge_of_forall_exists_gt [Preorder α] (h : ∀ a, ∃ b ∈ s, b < a) :
    Unbounded (· ≥ ·) s :=
  @unbounded_le_of_forall_exists_lt αᵒᵈ _ _ h
#align set.unbounded_ge_of_forall_exists_gt Set.unbounded_ge_of_forall_exists_gt

/- warning: set.unbounded_ge_iff -> Set.unbounded_ge_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α], Iff (Set.Unbounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s) (forall (a : α), Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b a)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α], Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.542 : α) (x._@.Mathlib.Order.Bounded._hyg.544 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.542 x._@.Mathlib.Order.Bounded._hyg.544) s) (forall (a : α), Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b a)))
Case conversion may be inaccurate. Consider using '#align set.unbounded_ge_iff Set.unbounded_ge_iffₓ'. -/
theorem unbounded_ge_iff [LinearOrder α] : Unbounded (· ≥ ·) s ↔ ∀ a, ∃ b ∈ s, b < a :=
  ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, lt_of_not_ge hba⟩,
    unbounded_ge_of_forall_exists_gt⟩
#align set.unbounded_ge_iff Set.unbounded_ge_iff

/- warning: set.unbounded_gt_of_forall_exists_ge -> Set.unbounded_gt_of_forall_exists_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α], (forall (a : α), Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b a))) -> (Set.Unbounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α _inst_1)) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α], (forall (a : α), Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b a))) -> (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.668 : α) (x._@.Mathlib.Order.Bounded._hyg.670 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α _inst_1) x._@.Mathlib.Order.Bounded._hyg.668 x._@.Mathlib.Order.Bounded._hyg.670) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_gt_of_forall_exists_ge Set.unbounded_gt_of_forall_exists_geₓ'. -/
theorem unbounded_gt_of_forall_exists_ge [Preorder α] (h : ∀ a, ∃ b ∈ s, b ≤ a) :
    Unbounded (· > ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => not_le_of_gt hba hb'⟩
#align set.unbounded_gt_of_forall_exists_ge Set.unbounded_gt_of_forall_exists_ge

/- warning: set.unbounded_gt_iff -> Set.unbounded_gt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α], Iff (Set.Unbounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s) (forall (a : α), Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b a)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α], Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.745 : α) (x._@.Mathlib.Order.Bounded._hyg.747 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.745 x._@.Mathlib.Order.Bounded._hyg.747) s) (forall (a : α), Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b a)))
Case conversion may be inaccurate. Consider using '#align set.unbounded_gt_iff Set.unbounded_gt_iffₓ'. -/
theorem unbounded_gt_iff [LinearOrder α] : Unbounded (· > ·) s ↔ ∀ a, ∃ b ∈ s, b ≤ a :=
  ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, le_of_not_gt hba⟩,
    unbounded_gt_of_forall_exists_ge⟩
#align set.unbounded_gt_iff Set.unbounded_gt_iff

/-! ### Relation between boundedness by strict and nonstrict orders. -/


/-! #### Less and less or equal -/


#print Set.Bounded.rel_mono /-
theorem Bounded.rel_mono {r' : α → α → Prop} (h : Bounded r s) (hrr' : r ≤ r') : Bounded r' s :=
  let ⟨a, ha⟩ := h
  ⟨a, fun b hb => hrr' b a (ha b hb)⟩
#align set.bounded.rel_mono Set.Bounded.rel_mono
-/

#print Set.bounded_le_of_bounded_lt /-
theorem bounded_le_of_bounded_lt [Preorder α] (h : Bounded (· < ·) s) : Bounded (· ≤ ·) s :=
  h.rel_mono fun _ _ => le_of_lt
#align set.bounded_le_of_bounded_lt Set.bounded_le_of_bounded_lt
-/

#print Set.Unbounded.rel_mono /-
theorem Unbounded.rel_mono {r' : α → α → Prop} (hr : r' ≤ r) (h : Unbounded r s) : Unbounded r' s :=
  fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (hr b a hba')⟩
#align set.unbounded.rel_mono Set.Unbounded.rel_mono
-/

#print Set.unbounded_lt_of_unbounded_le /-
theorem unbounded_lt_of_unbounded_le [Preorder α] (h : Unbounded (· ≤ ·) s) : Unbounded (· < ·) s :=
  h.rel_mono fun _ _ => le_of_lt
#align set.unbounded_lt_of_unbounded_le Set.unbounded_lt_of_unbounded_le
-/

#print Set.bounded_le_iff_bounded_lt /-
theorem bounded_le_iff_bounded_lt [Preorder α] [NoMaxOrder α] :
    Bounded (· ≤ ·) s ↔ Bounded (· < ·) s :=
  by
  refine' ⟨fun h => _, bounded_le_of_bounded_lt⟩
  cases' h with a ha
  cases' exists_gt a with b hb
  exact ⟨b, fun c hc => lt_of_le_of_lt (ha c hc) hb⟩
#align set.bounded_le_iff_bounded_lt Set.bounded_le_iff_bounded_lt
-/

#print Set.unbounded_lt_iff_unbounded_le /-
theorem unbounded_lt_iff_unbounded_le [Preorder α] [NoMaxOrder α] :
    Unbounded (· < ·) s ↔ Unbounded (· ≤ ·) s := by
  simp_rw [← not_bounded_iff, bounded_le_iff_bounded_lt]
#align set.unbounded_lt_iff_unbounded_le Set.unbounded_lt_iff_unbounded_le
-/

/-! #### Greater and greater or equal -/


#print Set.bounded_ge_of_bounded_gt /-
theorem bounded_ge_of_bounded_gt [Preorder α] (h : Bounded (· > ·) s) : Bounded (· ≥ ·) s :=
  let ⟨a, ha⟩ := h
  ⟨a, fun b hb => le_of_lt (ha b hb)⟩
#align set.bounded_ge_of_bounded_gt Set.bounded_ge_of_bounded_gt
-/

#print Set.unbounded_gt_of_unbounded_ge /-
theorem unbounded_gt_of_unbounded_ge [Preorder α] (h : Unbounded (· ≥ ·) s) : Unbounded (· > ·) s :=
  fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (le_of_lt hba')⟩
#align set.unbounded_gt_of_unbounded_ge Set.unbounded_gt_of_unbounded_ge
-/

#print Set.bounded_ge_iff_bounded_gt /-
theorem bounded_ge_iff_bounded_gt [Preorder α] [NoMinOrder α] :
    Bounded (· ≥ ·) s ↔ Bounded (· > ·) s :=
  @bounded_le_iff_bounded_lt αᵒᵈ _ _ _
#align set.bounded_ge_iff_bounded_gt Set.bounded_ge_iff_bounded_gt
-/

#print Set.unbounded_gt_iff_unbounded_ge /-
theorem unbounded_gt_iff_unbounded_ge [Preorder α] [NoMinOrder α] :
    Unbounded (· > ·) s ↔ Unbounded (· ≥ ·) s :=
  @unbounded_lt_iff_unbounded_le αᵒᵈ _ _ _
#align set.unbounded_gt_iff_unbounded_ge Set.unbounded_gt_iff_unbounded_ge
-/

/-! ### The universal set -/


#print Set.unbounded_le_univ /-
theorem unbounded_le_univ [LE α] [NoTopOrder α] : Unbounded (· ≤ ·) (@Set.univ α) := fun a =>
  let ⟨b, hb⟩ := exists_not_le a
  ⟨b, ⟨⟩, hb⟩
#align set.unbounded_le_univ Set.unbounded_le_univ
-/

#print Set.unbounded_lt_univ /-
theorem unbounded_lt_univ [Preorder α] [NoTopOrder α] : Unbounded (· < ·) (@Set.univ α) :=
  unbounded_lt_of_unbounded_le unbounded_le_univ
#align set.unbounded_lt_univ Set.unbounded_lt_univ
-/

#print Set.unbounded_ge_univ /-
theorem unbounded_ge_univ [LE α] [NoBotOrder α] : Unbounded (· ≥ ·) (@Set.univ α) := fun a =>
  let ⟨b, hb⟩ := exists_not_ge a
  ⟨b, ⟨⟩, hb⟩
#align set.unbounded_ge_univ Set.unbounded_ge_univ
-/

#print Set.unbounded_gt_univ /-
theorem unbounded_gt_univ [Preorder α] [NoBotOrder α] : Unbounded (· > ·) (@Set.univ α) :=
  unbounded_gt_of_unbounded_ge unbounded_ge_univ
#align set.unbounded_gt_univ Set.unbounded_gt_univ
-/

/-! ### Bounded and unbounded intervals -/


#print Set.bounded_self /-
theorem bounded_self (a : α) : Bounded r { b | r b a } :=
  ⟨a, fun x => id⟩
#align set.bounded_self Set.bounded_self
-/

/-! #### Half-open bounded intervals -/


#print Set.bounded_lt_Iio /-
theorem bounded_lt_Iio [Preorder α] (a : α) : Bounded (· < ·) (Set.Iio a) :=
  bounded_self a
#align set.bounded_lt_Iio Set.bounded_lt_Iio
-/

#print Set.bounded_le_Iio /-
theorem bounded_le_Iio [Preorder α] (a : α) : Bounded (· ≤ ·) (Set.Iio a) :=
  bounded_le_of_bounded_lt (bounded_lt_Iio a)
#align set.bounded_le_Iio Set.bounded_le_Iio
-/

#print Set.bounded_le_Iic /-
theorem bounded_le_Iic [Preorder α] (a : α) : Bounded (· ≤ ·) (Set.Iic a) :=
  bounded_self a
#align set.bounded_le_Iic Set.bounded_le_Iic
-/

#print Set.bounded_lt_Iic /-
theorem bounded_lt_Iic [Preorder α] [NoMaxOrder α] (a : α) : Bounded (· < ·) (Set.Iic a) := by
  simp only [← bounded_le_iff_bounded_lt, bounded_le_Iic]
#align set.bounded_lt_Iic Set.bounded_lt_Iic
-/

#print Set.bounded_gt_Ioi /-
theorem bounded_gt_Ioi [Preorder α] (a : α) : Bounded (· > ·) (Set.Ioi a) :=
  bounded_self a
#align set.bounded_gt_Ioi Set.bounded_gt_Ioi
-/

#print Set.bounded_ge_Ioi /-
theorem bounded_ge_Ioi [Preorder α] (a : α) : Bounded (· ≥ ·) (Set.Ioi a) :=
  bounded_ge_of_bounded_gt (bounded_gt_Ioi a)
#align set.bounded_ge_Ioi Set.bounded_ge_Ioi
-/

#print Set.bounded_ge_Ici /-
theorem bounded_ge_Ici [Preorder α] (a : α) : Bounded (· ≥ ·) (Set.Ici a) :=
  bounded_self a
#align set.bounded_ge_Ici Set.bounded_ge_Ici
-/

#print Set.bounded_gt_Ici /-
theorem bounded_gt_Ici [Preorder α] [NoMinOrder α] (a : α) : Bounded (· > ·) (Set.Ici a) := by
  simp only [← bounded_ge_iff_bounded_gt, bounded_ge_Ici]
#align set.bounded_gt_Ici Set.bounded_gt_Ici
-/

/-! #### Other bounded intervals -/


#print Set.bounded_lt_Ioo /-
theorem bounded_lt_Ioo [Preorder α] (a b : α) : Bounded (· < ·) (Set.Ioo a b) :=
  (bounded_lt_Iio b).mono Set.Ioo_subset_Iio_self
#align set.bounded_lt_Ioo Set.bounded_lt_Ioo
-/

#print Set.bounded_lt_Ico /-
theorem bounded_lt_Ico [Preorder α] (a b : α) : Bounded (· < ·) (Set.Ico a b) :=
  (bounded_lt_Iio b).mono Set.Ico_subset_Iio_self
#align set.bounded_lt_Ico Set.bounded_lt_Ico
-/

#print Set.bounded_lt_Ioc /-
theorem bounded_lt_Ioc [Preorder α] [NoMaxOrder α] (a b : α) : Bounded (· < ·) (Set.Ioc a b) :=
  (bounded_lt_Iic b).mono Set.Ioc_subset_Iic_self
#align set.bounded_lt_Ioc Set.bounded_lt_Ioc
-/

#print Set.bounded_lt_Icc /-
theorem bounded_lt_Icc [Preorder α] [NoMaxOrder α] (a b : α) : Bounded (· < ·) (Set.Icc a b) :=
  (bounded_lt_Iic b).mono Set.Icc_subset_Iic_self
#align set.bounded_lt_Icc Set.bounded_lt_Icc
-/

#print Set.bounded_le_Ioo /-
theorem bounded_le_Ioo [Preorder α] (a b : α) : Bounded (· ≤ ·) (Set.Ioo a b) :=
  (bounded_le_Iio b).mono Set.Ioo_subset_Iio_self
#align set.bounded_le_Ioo Set.bounded_le_Ioo
-/

#print Set.bounded_le_Ico /-
theorem bounded_le_Ico [Preorder α] (a b : α) : Bounded (· ≤ ·) (Set.Ico a b) :=
  (bounded_le_Iio b).mono Set.Ico_subset_Iio_self
#align set.bounded_le_Ico Set.bounded_le_Ico
-/

#print Set.bounded_le_Ioc /-
theorem bounded_le_Ioc [Preorder α] (a b : α) : Bounded (· ≤ ·) (Set.Ioc a b) :=
  (bounded_le_Iic b).mono Set.Ioc_subset_Iic_self
#align set.bounded_le_Ioc Set.bounded_le_Ioc
-/

#print Set.bounded_le_Icc /-
theorem bounded_le_Icc [Preorder α] (a b : α) : Bounded (· ≤ ·) (Set.Icc a b) :=
  (bounded_le_Iic b).mono Set.Icc_subset_Iic_self
#align set.bounded_le_Icc Set.bounded_le_Icc
-/

#print Set.bounded_gt_Ioo /-
theorem bounded_gt_Ioo [Preorder α] (a b : α) : Bounded (· > ·) (Set.Ioo a b) :=
  (bounded_gt_Ioi a).mono Set.Ioo_subset_Ioi_self
#align set.bounded_gt_Ioo Set.bounded_gt_Ioo
-/

#print Set.bounded_gt_Ioc /-
theorem bounded_gt_Ioc [Preorder α] (a b : α) : Bounded (· > ·) (Set.Ioc a b) :=
  (bounded_gt_Ioi a).mono Set.Ioc_subset_Ioi_self
#align set.bounded_gt_Ioc Set.bounded_gt_Ioc
-/

#print Set.bounded_gt_Ico /-
theorem bounded_gt_Ico [Preorder α] [NoMinOrder α] (a b : α) : Bounded (· > ·) (Set.Ico a b) :=
  (bounded_gt_Ici a).mono Set.Ico_subset_Ici_self
#align set.bounded_gt_Ico Set.bounded_gt_Ico
-/

#print Set.bounded_gt_Icc /-
theorem bounded_gt_Icc [Preorder α] [NoMinOrder α] (a b : α) : Bounded (· > ·) (Set.Icc a b) :=
  (bounded_gt_Ici a).mono Set.Icc_subset_Ici_self
#align set.bounded_gt_Icc Set.bounded_gt_Icc
-/

#print Set.bounded_ge_Ioo /-
theorem bounded_ge_Ioo [Preorder α] (a b : α) : Bounded (· ≥ ·) (Set.Ioo a b) :=
  (bounded_ge_Ioi a).mono Set.Ioo_subset_Ioi_self
#align set.bounded_ge_Ioo Set.bounded_ge_Ioo
-/

#print Set.bounded_ge_Ioc /-
theorem bounded_ge_Ioc [Preorder α] (a b : α) : Bounded (· ≥ ·) (Set.Ioc a b) :=
  (bounded_ge_Ioi a).mono Set.Ioc_subset_Ioi_self
#align set.bounded_ge_Ioc Set.bounded_ge_Ioc
-/

#print Set.bounded_ge_Ico /-
theorem bounded_ge_Ico [Preorder α] (a b : α) : Bounded (· ≥ ·) (Set.Ico a b) :=
  (bounded_ge_Ici a).mono Set.Ico_subset_Ici_self
#align set.bounded_ge_Ico Set.bounded_ge_Ico
-/

#print Set.bounded_ge_Icc /-
theorem bounded_ge_Icc [Preorder α] (a b : α) : Bounded (· ≥ ·) (Set.Icc a b) :=
  (bounded_ge_Ici a).mono Set.Icc_subset_Ici_self
#align set.bounded_ge_Icc Set.bounded_ge_Icc
-/

/-! #### Unbounded intervals -/


#print Set.unbounded_le_Ioi /-
theorem unbounded_le_Ioi [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· ≤ ·) (Set.Ioi a) := fun b =>
  let ⟨c, hc⟩ := exists_gt (a ⊔ b)
  ⟨c, le_sup_left.trans_lt hc, (le_sup_right.trans_lt hc).not_le⟩
#align set.unbounded_le_Ioi Set.unbounded_le_Ioi
-/

#print Set.unbounded_le_Ici /-
theorem unbounded_le_Ici [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· ≤ ·) (Set.Ici a) :=
  (unbounded_le_Ioi a).mono Set.Ioi_subset_Ici_self
#align set.unbounded_le_Ici Set.unbounded_le_Ici
-/

#print Set.unbounded_lt_Ioi /-
theorem unbounded_lt_Ioi [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· < ·) (Set.Ioi a) :=
  unbounded_lt_of_unbounded_le (unbounded_le_Ioi a)
#align set.unbounded_lt_Ioi Set.unbounded_lt_Ioi
-/

#print Set.unbounded_lt_Ici /-
theorem unbounded_lt_Ici [SemilatticeSup α] (a : α) : Unbounded (· < ·) (Set.Ici a) := fun b =>
  ⟨a ⊔ b, le_sup_left, le_sup_right.not_lt⟩
#align set.unbounded_lt_Ici Set.unbounded_lt_Ici
-/

/-! ### Bounded initial segments -/


/- warning: set.bounded_inter_not -> Set.bounded_inter_not is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α}, (forall (a : α) (b : α), Exists.{succ u1} α (fun (m : α) => forall (c : α), (Or (r c a) (r c b)) -> (r c m))) -> (forall (a : α), Iff (Set.Bounded.{u1} α r (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (r b a))))) (Set.Bounded.{u1} α r s))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α}, (forall (a : α) (b : α), Exists.{succ u1} α (fun (m : α) => forall (c : α), (Or (r c a) (r c b)) -> (r c m))) -> (forall (a : α), Iff (Set.Bounded.{u1} α r (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (r b a))))) (Set.Bounded.{u1} α r s))
Case conversion may be inaccurate. Consider using '#align set.bounded_inter_not Set.bounded_inter_notₓ'. -/
theorem bounded_inter_not (H : ∀ a b, ∃ m, ∀ c, r c a ∨ r c b → r c m) (a : α) :
    Bounded r (s ∩ { b | ¬r b a }) ↔ Bounded r s :=
  by
  refine' ⟨_, bounded.mono (Set.inter_subset_left s _)⟩
  rintro ⟨b, hb⟩
  cases' H a b with m hm
  exact ⟨m, fun c hc => hm c (or_iff_not_imp_left.2 fun hca => hb c ⟨hc, hca⟩)⟩
#align set.bounded_inter_not Set.bounded_inter_not

/- warning: set.unbounded_inter_not -> Set.unbounded_inter_not is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α}, (forall (a : α) (b : α), Exists.{succ u1} α (fun (m : α) => forall (c : α), (Or (r c a) (r c b)) -> (r c m))) -> (forall (a : α), Iff (Set.Unbounded.{u1} α r (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (r b a))))) (Set.Unbounded.{u1} α r s))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α}, (forall (a : α) (b : α), Exists.{succ u1} α (fun (m : α) => forall (c : α), (Or (r c a) (r c b)) -> (r c m))) -> (forall (a : α), Iff (Set.Unbounded.{u1} α r (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (r b a))))) (Set.Unbounded.{u1} α r s))
Case conversion may be inaccurate. Consider using '#align set.unbounded_inter_not Set.unbounded_inter_notₓ'. -/
theorem unbounded_inter_not (H : ∀ a b, ∃ m, ∀ c, r c a ∨ r c b → r c m) (a : α) :
    Unbounded r (s ∩ { b | ¬r b a }) ↔ Unbounded r s := by
  simp_rw [← not_bounded_iff, bounded_inter_not H]
#align set.unbounded_inter_not Set.unbounded_inter_not

/-! #### Less or equal -/


/- warning: set.bounded_le_inter_not_le -> Set.bounded_le_inter_not_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeSup.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))))) (Set.Bounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeSup.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3253 : α) (x._@.Mathlib.Order.Bounded._hyg.3255 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.3253 x._@.Mathlib.Order.Bounded._hyg.3255) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3289 : α) (x._@.Mathlib.Order.Bounded._hyg.3291 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.3289 x._@.Mathlib.Order.Bounded._hyg.3291) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_le_inter_not_le Set.bounded_le_inter_not_leₓ'. -/
theorem bounded_le_inter_not_le [SemilatticeSup α] (a : α) :
    Bounded (· ≤ ·) (s ∩ { b | ¬b ≤ a }) ↔ Bounded (· ≤ ·) s :=
  bounded_inter_not (fun x y => ⟨x ⊔ y, fun z h => h.elim le_sup_of_le_left le_sup_of_le_right⟩) a
#align set.bounded_le_inter_not_le Set.bounded_le_inter_not_le

/- warning: set.unbounded_le_inter_not_le -> Set.unbounded_le_inter_not_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeSup.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))))) (Set.Unbounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeSup.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3348 : α) (x._@.Mathlib.Order.Bounded._hyg.3350 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.3348 x._@.Mathlib.Order.Bounded._hyg.3350) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3384 : α) (x._@.Mathlib.Order.Bounded._hyg.3386 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.3384 x._@.Mathlib.Order.Bounded._hyg.3386) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_le_inter_not_le Set.unbounded_le_inter_not_leₓ'. -/
theorem unbounded_le_inter_not_le [SemilatticeSup α] (a : α) :
    Unbounded (· ≤ ·) (s ∩ { b | ¬b ≤ a }) ↔ Unbounded (· ≤ ·) s :=
  by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_le_inter_not_le a
#align set.unbounded_le_inter_not_le Set.unbounded_le_inter_not_le

/- warning: set.bounded_le_inter_lt -> Set.bounded_le_inter_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)))) (Set.Bounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3457 : α) (x._@.Mathlib.Order.Bounded._hyg.3459 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.3457 x._@.Mathlib.Order.Bounded._hyg.3459) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3490 : α) (x._@.Mathlib.Order.Bounded._hyg.3492 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.3490 x._@.Mathlib.Order.Bounded._hyg.3492) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_le_inter_lt Set.bounded_le_inter_ltₓ'. -/
theorem bounded_le_inter_lt [LinearOrder α] (a : α) :
    Bounded (· ≤ ·) (s ∩ { b | a < b }) ↔ Bounded (· ≤ ·) s := by
  simp_rw [← not_le, bounded_le_inter_not_le]
#align set.bounded_le_inter_lt Set.bounded_le_inter_lt

/- warning: set.unbounded_le_inter_lt -> Set.unbounded_le_inter_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)))) (Set.Unbounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3535 : α) (x._@.Mathlib.Order.Bounded._hyg.3537 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.3535 x._@.Mathlib.Order.Bounded._hyg.3537) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3568 : α) (x._@.Mathlib.Order.Bounded._hyg.3570 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.3568 x._@.Mathlib.Order.Bounded._hyg.3570) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_le_inter_lt Set.unbounded_le_inter_ltₓ'. -/
theorem unbounded_le_inter_lt [LinearOrder α] (a : α) :
    Unbounded (· ≤ ·) (s ∩ { b | a < b }) ↔ Unbounded (· ≤ ·) s :=
  by
  convert unbounded_le_inter_not_le a
  ext
  exact lt_iff_not_le
#align set.unbounded_le_inter_lt Set.unbounded_le_inter_lt

/- warning: set.bounded_le_inter_le -> Set.bounded_le_inter_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)))) (Set.Bounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3621 : α) (x._@.Mathlib.Order.Bounded._hyg.3623 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.3621 x._@.Mathlib.Order.Bounded._hyg.3623) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3654 : α) (x._@.Mathlib.Order.Bounded._hyg.3656 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.3654 x._@.Mathlib.Order.Bounded._hyg.3656) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_le_inter_le Set.bounded_le_inter_leₓ'. -/
theorem bounded_le_inter_le [LinearOrder α] (a : α) :
    Bounded (· ≤ ·) (s ∩ { b | a ≤ b }) ↔ Bounded (· ≤ ·) s :=
  by
  refine' ⟨_, bounded.mono (Set.inter_subset_left s _)⟩
  rw [← @bounded_le_inter_lt _ s _ a]
  exact bounded.mono fun x ⟨hx, hx'⟩ => ⟨hx, le_of_lt hx'⟩
#align set.bounded_le_inter_le Set.bounded_le_inter_le

/- warning: set.unbounded_le_inter_le -> Set.unbounded_le_inter_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)))) (Set.Unbounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3763 : α) (x._@.Mathlib.Order.Bounded._hyg.3765 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.3763 x._@.Mathlib.Order.Bounded._hyg.3765) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3796 : α) (x._@.Mathlib.Order.Bounded._hyg.3798 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.3796 x._@.Mathlib.Order.Bounded._hyg.3798) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_le_inter_le Set.unbounded_le_inter_leₓ'. -/
theorem unbounded_le_inter_le [LinearOrder α] (a : α) :
    Unbounded (· ≤ ·) (s ∩ { b | a ≤ b }) ↔ Unbounded (· ≤ ·) s :=
  by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_le_inter_le a
#align set.unbounded_le_inter_le Set.unbounded_le_inter_le

/-! #### Less than -/


/- warning: set.bounded_lt_inter_not_lt -> Set.bounded_lt_inter_not_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeSup.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))))) (Set.Bounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeSup.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3870 : α) (x._@.Mathlib.Order.Bounded._hyg.3872 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.3870 x._@.Mathlib.Order.Bounded._hyg.3872) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3906 : α) (x._@.Mathlib.Order.Bounded._hyg.3908 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.3906 x._@.Mathlib.Order.Bounded._hyg.3908) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_lt_inter_not_lt Set.bounded_lt_inter_not_ltₓ'. -/
theorem bounded_lt_inter_not_lt [SemilatticeSup α] (a : α) :
    Bounded (· < ·) (s ∩ { b | ¬b < a }) ↔ Bounded (· < ·) s :=
  bounded_inter_not (fun x y => ⟨x ⊔ y, fun z h => h.elim lt_sup_of_lt_left lt_sup_of_lt_right⟩) a
#align set.bounded_lt_inter_not_lt Set.bounded_lt_inter_not_lt

/- warning: set.unbounded_lt_inter_not_lt -> Set.unbounded_lt_inter_not_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeSup.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))))) (Set.Unbounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeSup.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.3965 : α) (x._@.Mathlib.Order.Bounded._hyg.3967 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.3965 x._@.Mathlib.Order.Bounded._hyg.3967) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4001 : α) (x._@.Mathlib.Order.Bounded._hyg.4003 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.4001 x._@.Mathlib.Order.Bounded._hyg.4003) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_lt_inter_not_lt Set.unbounded_lt_inter_not_ltₓ'. -/
theorem unbounded_lt_inter_not_lt [SemilatticeSup α] (a : α) :
    Unbounded (· < ·) (s ∩ { b | ¬b < a }) ↔ Unbounded (· < ·) s :=
  by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_lt_inter_not_lt a
#align set.unbounded_lt_inter_not_lt Set.unbounded_lt_inter_not_lt

/- warning: set.bounded_lt_inter_le -> Set.bounded_lt_inter_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)))) (Set.Bounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4074 : α) (x._@.Mathlib.Order.Bounded._hyg.4076 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4074 x._@.Mathlib.Order.Bounded._hyg.4076) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4107 : α) (x._@.Mathlib.Order.Bounded._hyg.4109 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4107 x._@.Mathlib.Order.Bounded._hyg.4109) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_lt_inter_le Set.bounded_lt_inter_leₓ'. -/
theorem bounded_lt_inter_le [LinearOrder α] (a : α) :
    Bounded (· < ·) (s ∩ { b | a ≤ b }) ↔ Bounded (· < ·) s :=
  by
  convert bounded_lt_inter_not_lt a
  ext
  exact not_lt.symm
#align set.bounded_lt_inter_le Set.bounded_lt_inter_le

/- warning: set.unbounded_lt_inter_le -> Set.unbounded_lt_inter_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)))) (Set.Unbounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4160 : α) (x._@.Mathlib.Order.Bounded._hyg.4162 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4160 x._@.Mathlib.Order.Bounded._hyg.4162) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4193 : α) (x._@.Mathlib.Order.Bounded._hyg.4195 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4193 x._@.Mathlib.Order.Bounded._hyg.4195) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_lt_inter_le Set.unbounded_lt_inter_leₓ'. -/
theorem unbounded_lt_inter_le [LinearOrder α] (a : α) :
    Unbounded (· < ·) (s ∩ { b | a ≤ b }) ↔ Unbounded (· < ·) s :=
  by
  convert unbounded_lt_inter_not_lt a
  ext
  exact not_lt.symm
#align set.unbounded_lt_inter_le Set.unbounded_lt_inter_le

/- warning: set.bounded_lt_inter_lt -> Set.bounded_lt_inter_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] (a : α), Iff (Set.Bounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)))) (Set.Bounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4249 : α) (x._@.Mathlib.Order.Bounded._hyg.4251 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4249 x._@.Mathlib.Order.Bounded._hyg.4251) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4282 : α) (x._@.Mathlib.Order.Bounded._hyg.4284 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4282 x._@.Mathlib.Order.Bounded._hyg.4284) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_lt_inter_lt Set.bounded_lt_inter_ltₓ'. -/
theorem bounded_lt_inter_lt [LinearOrder α] [NoMaxOrder α] (a : α) :
    Bounded (· < ·) (s ∩ { b | a < b }) ↔ Bounded (· < ·) s :=
  by
  rw [← bounded_le_iff_bounded_lt, ← bounded_le_iff_bounded_lt]
  exact bounded_le_inter_lt a
#align set.bounded_lt_inter_lt Set.bounded_lt_inter_lt

/- warning: set.unbounded_lt_inter_lt -> Set.unbounded_lt_inter_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] (a : α), Iff (Set.Unbounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)))) (Set.Unbounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4357 : α) (x._@.Mathlib.Order.Bounded._hyg.4359 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4357 x._@.Mathlib.Order.Bounded._hyg.4359) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4390 : α) (x._@.Mathlib.Order.Bounded._hyg.4392 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4390 x._@.Mathlib.Order.Bounded._hyg.4392) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_lt_inter_lt Set.unbounded_lt_inter_ltₓ'. -/
theorem unbounded_lt_inter_lt [LinearOrder α] [NoMaxOrder α] (a : α) :
    Unbounded (· < ·) (s ∩ { b | a < b }) ↔ Unbounded (· < ·) s :=
  by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_lt_inter_lt a
#align set.unbounded_lt_inter_lt Set.unbounded_lt_inter_lt

/-! #### Greater or equal -/


/- warning: set.bounded_ge_inter_not_ge -> Set.bounded_ge_inter_not_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeInf.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))))) (Set.Bounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeInf.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4464 : α) (x._@.Mathlib.Order.Bounded._hyg.4466 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.4464 x._@.Mathlib.Order.Bounded._hyg.4466) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4500 : α) (x._@.Mathlib.Order.Bounded._hyg.4502 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.4500 x._@.Mathlib.Order.Bounded._hyg.4502) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_ge_inter_not_ge Set.bounded_ge_inter_not_geₓ'. -/
theorem bounded_ge_inter_not_ge [SemilatticeInf α] (a : α) :
    Bounded (· ≥ ·) (s ∩ { b | ¬a ≤ b }) ↔ Bounded (· ≥ ·) s :=
  @bounded_le_inter_not_le αᵒᵈ s _ a
#align set.bounded_ge_inter_not_ge Set.bounded_ge_inter_not_ge

/- warning: set.unbounded_ge_inter_not_ge -> Set.unbounded_ge_inter_not_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeInf.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))))) (Set.Unbounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeInf.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4543 : α) (x._@.Mathlib.Order.Bounded._hyg.4545 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.4543 x._@.Mathlib.Order.Bounded._hyg.4545) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4579 : α) (x._@.Mathlib.Order.Bounded._hyg.4581 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.4579 x._@.Mathlib.Order.Bounded._hyg.4581) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_ge_inter_not_ge Set.unbounded_ge_inter_not_geₓ'. -/
theorem unbounded_ge_inter_not_ge [SemilatticeInf α] (a : α) :
    Unbounded (· ≥ ·) (s ∩ { b | ¬a ≤ b }) ↔ Unbounded (· ≥ ·) s :=
  @unbounded_le_inter_not_le αᵒᵈ s _ a
#align set.unbounded_ge_inter_not_ge Set.unbounded_ge_inter_not_ge

/- warning: set.bounded_ge_inter_gt -> Set.bounded_ge_inter_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b a)))) (Set.Bounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4622 : α) (x._@.Mathlib.Order.Bounded._hyg.4624 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4622 x._@.Mathlib.Order.Bounded._hyg.4624) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b a)))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4655 : α) (x._@.Mathlib.Order.Bounded._hyg.4657 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4655 x._@.Mathlib.Order.Bounded._hyg.4657) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_ge_inter_gt Set.bounded_ge_inter_gtₓ'. -/
theorem bounded_ge_inter_gt [LinearOrder α] (a : α) :
    Bounded (· ≥ ·) (s ∩ { b | b < a }) ↔ Bounded (· ≥ ·) s :=
  @bounded_le_inter_lt αᵒᵈ s _ a
#align set.bounded_ge_inter_gt Set.bounded_ge_inter_gt

/- warning: set.unbounded_ge_inter_gt -> Set.unbounded_ge_inter_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b a)))) (Set.Unbounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4698 : α) (x._@.Mathlib.Order.Bounded._hyg.4700 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4698 x._@.Mathlib.Order.Bounded._hyg.4700) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b a)))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4731 : α) (x._@.Mathlib.Order.Bounded._hyg.4733 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4731 x._@.Mathlib.Order.Bounded._hyg.4733) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_ge_inter_gt Set.unbounded_ge_inter_gtₓ'. -/
theorem unbounded_ge_inter_gt [LinearOrder α] (a : α) :
    Unbounded (· ≥ ·) (s ∩ { b | b < a }) ↔ Unbounded (· ≥ ·) s :=
  @unbounded_le_inter_lt αᵒᵈ s _ a
#align set.unbounded_ge_inter_gt Set.unbounded_ge_inter_gt

/- warning: set.bounded_ge_inter_ge -> Set.bounded_ge_inter_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b a)))) (Set.Bounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4774 : α) (x._@.Mathlib.Order.Bounded._hyg.4776 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4774 x._@.Mathlib.Order.Bounded._hyg.4776) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b a)))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4807 : α) (x._@.Mathlib.Order.Bounded._hyg.4809 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4807 x._@.Mathlib.Order.Bounded._hyg.4809) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_ge_inter_ge Set.bounded_ge_inter_geₓ'. -/
theorem bounded_ge_inter_ge [LinearOrder α] (a : α) :
    Bounded (· ≥ ·) (s ∩ { b | b ≤ a }) ↔ Bounded (· ≥ ·) s :=
  @bounded_le_inter_le αᵒᵈ s _ a
#align set.bounded_ge_inter_ge Set.bounded_ge_inter_ge

/- warning: set.unbounded_ge_iff_unbounded_inter_ge -> Set.unbounded_ge_iff_unbounded_inter_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b a)))) (Set.Unbounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4850 : α) (x._@.Mathlib.Order.Bounded._hyg.4852 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4850 x._@.Mathlib.Order.Bounded._hyg.4852) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b a)))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4883 : α) (x._@.Mathlib.Order.Bounded._hyg.4885 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.4883 x._@.Mathlib.Order.Bounded._hyg.4885) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_ge_iff_unbounded_inter_ge Set.unbounded_ge_iff_unbounded_inter_geₓ'. -/
theorem unbounded_ge_iff_unbounded_inter_ge [LinearOrder α] (a : α) :
    Unbounded (· ≥ ·) (s ∩ { b | b ≤ a }) ↔ Unbounded (· ≥ ·) s :=
  @unbounded_le_inter_le αᵒᵈ s _ a
#align set.unbounded_ge_iff_unbounded_inter_ge Set.unbounded_ge_iff_unbounded_inter_ge

/-! #### Greater than -/


/- warning: set.bounded_gt_inter_not_gt -> Set.bounded_gt_inter_not_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeInf.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))))) (Set.Bounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeInf.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4927 : α) (x._@.Mathlib.Order.Bounded._hyg.4929 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.4927 x._@.Mathlib.Order.Bounded._hyg.4929) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.4963 : α) (x._@.Mathlib.Order.Bounded._hyg.4965 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.4963 x._@.Mathlib.Order.Bounded._hyg.4965) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_gt_inter_not_gt Set.bounded_gt_inter_not_gtₓ'. -/
theorem bounded_gt_inter_not_gt [SemilatticeInf α] (a : α) :
    Bounded (· > ·) (s ∩ { b | ¬a < b }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_not_lt αᵒᵈ s _ a
#align set.bounded_gt_inter_not_gt Set.bounded_gt_inter_not_gt

/- warning: set.unbounded_gt_inter_not_gt -> Set.unbounded_gt_inter_not_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeInf.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))))) (Set.Unbounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : SemilatticeInf.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.5006 : α) (x._@.Mathlib.Order.Bounded._hyg.5008 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.5006 x._@.Mathlib.Order.Bounded._hyg.5008) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.5042 : α) (x._@.Mathlib.Order.Bounded._hyg.5044 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Bounded._hyg.5042 x._@.Mathlib.Order.Bounded._hyg.5044) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_gt_inter_not_gt Set.unbounded_gt_inter_not_gtₓ'. -/
theorem unbounded_gt_inter_not_gt [SemilatticeInf α] (a : α) :
    Unbounded (· > ·) (s ∩ { b | ¬a < b }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_not_lt αᵒᵈ s _ a
#align set.unbounded_gt_inter_not_gt Set.unbounded_gt_inter_not_gt

/- warning: set.bounded_gt_inter_ge -> Set.bounded_gt_inter_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b a)))) (Set.Bounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.5085 : α) (x._@.Mathlib.Order.Bounded._hyg.5087 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.5085 x._@.Mathlib.Order.Bounded._hyg.5087) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b a)))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.5118 : α) (x._@.Mathlib.Order.Bounded._hyg.5120 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.5118 x._@.Mathlib.Order.Bounded._hyg.5120) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_gt_inter_ge Set.bounded_gt_inter_geₓ'. -/
theorem bounded_gt_inter_ge [LinearOrder α] (a : α) :
    Bounded (· > ·) (s ∩ { b | b ≤ a }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_le αᵒᵈ s _ a
#align set.bounded_gt_inter_ge Set.bounded_gt_inter_ge

/- warning: set.unbounded_inter_ge -> Set.unbounded_inter_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b a)))) (Set.Unbounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.5161 : α) (x._@.Mathlib.Order.Bounded._hyg.5163 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.5161 x._@.Mathlib.Order.Bounded._hyg.5163) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b a)))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.5194 : α) (x._@.Mathlib.Order.Bounded._hyg.5196 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.5194 x._@.Mathlib.Order.Bounded._hyg.5196) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_inter_ge Set.unbounded_inter_geₓ'. -/
theorem unbounded_inter_ge [LinearOrder α] (a : α) :
    Unbounded (· > ·) (s ∩ { b | b ≤ a }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_le αᵒᵈ s _ a
#align set.unbounded_inter_ge Set.unbounded_inter_ge

/- warning: set.bounded_gt_inter_gt -> Set.bounded_gt_inter_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] (a : α), Iff (Set.Bounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b a)))) (Set.Bounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] (a : α), Iff (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.5240 : α) (x._@.Mathlib.Order.Bounded._hyg.5242 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.5240 x._@.Mathlib.Order.Bounded._hyg.5242) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b a)))) (Set.Bounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.5273 : α) (x._@.Mathlib.Order.Bounded._hyg.5275 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.5273 x._@.Mathlib.Order.Bounded._hyg.5275) s)
Case conversion may be inaccurate. Consider using '#align set.bounded_gt_inter_gt Set.bounded_gt_inter_gtₓ'. -/
theorem bounded_gt_inter_gt [LinearOrder α] [NoMinOrder α] (a : α) :
    Bounded (· > ·) (s ∩ { b | b < a }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_lt αᵒᵈ s _ _ a
#align set.bounded_gt_inter_gt Set.bounded_gt_inter_gt

/- warning: set.unbounded_gt_inter_gt -> Set.unbounded_gt_inter_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] (a : α), Iff (Set.Unbounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b a)))) (Set.Unbounded.{u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] (a : α), Iff (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.5319 : α) (x._@.Mathlib.Order.Bounded._hyg.5321 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.5319 x._@.Mathlib.Order.Bounded._hyg.5321) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b a)))) (Set.Unbounded.{u1} α (fun (x._@.Mathlib.Order.Bounded._hyg.5352 : α) (x._@.Mathlib.Order.Bounded._hyg.5354 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Bounded._hyg.5352 x._@.Mathlib.Order.Bounded._hyg.5354) s)
Case conversion may be inaccurate. Consider using '#align set.unbounded_gt_inter_gt Set.unbounded_gt_inter_gtₓ'. -/
theorem unbounded_gt_inter_gt [LinearOrder α] [NoMinOrder α] (a : α) :
    Unbounded (· > ·) (s ∩ { b | b < a }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_lt αᵒᵈ s _ _ a
#align set.unbounded_gt_inter_gt Set.unbounded_gt_inter_gt

end Set

