/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou

! This file was ported from Lean 3 source module data.set.intervals.unordered_interval
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Bounds.Basic
import Mathbin.Data.Set.Intervals.Basic

/-!
# Intervals without endpoints ordering

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In any lattice `α`, we define `uIcc a b` to be `Icc (a ⊓ b) (a ⊔ b)`, which in a linear order is the
set of elements lying between `a` and `b`.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. The
interval as defined in this file is always the set of things lying between `a` and `b`, regardless
of the relative order of `a` and `b`.

For real numbers, `uIcc a b` is the same as `segment ℝ a b`.

In a product or pi type, `uIcc a b` is the smallest box containing `a` and `b`. For example,
`uIcc (1, -1) (-1, 1) = Icc (-1, -1) (1, 1)` is the square of vertices `(1, -1)`, `(-1, -1)`,
`(-1, 1)`, `(1, 1)`.

In `finset α` (seen as a hypercube of dimension `fintype.card α`), `uIcc a b` is the smallest
subcube containing both `a` and `b`.

## Notation

We use the localized notation `[a, b]` for `uIcc a b`. One can open the locale `interval` to
make the notation available.

-/


open Function

open OrderDual (toDual ofDual)

variable {α β : Type _}

namespace Set

section Lattice

variable [Lattice α] {a a₁ a₂ b b₁ b₂ c x : α}

#print Set.uIcc /-
/-- `uIcc a b` is the set of elements lying between `a` and `b`, with `a` and `b` included.
Note that we define it more generally in a lattice as `set.Icc (a ⊓ b) (a ⊔ b)`. In a product type,
`uIcc` corresponds to the bounding box of the two elements. -/
def uIcc (a b : α) : Set α :=
  Icc (a ⊓ b) (a ⊔ b)
#align set.uIcc Set.uIcc
-/

-- mathport name: set.uIcc
scoped[Interval] notation "[" a ", " b "]" => Set.uIcc a b

#print Set.dual_uIcc /-
@[simp]
theorem dual_uIcc (a b : α) : [toDual a, toDual b] = ofDual ⁻¹' [a, b] :=
  dual_Icc
#align set.dual_uIcc Set.dual_uIcc
-/

#print Set.uIcc_of_le /-
@[simp]
theorem uIcc_of_le (h : a ≤ b) : [a, b] = Icc a b := by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]
#align set.uIcc_of_le Set.uIcc_of_le
-/

#print Set.uIcc_of_ge /-
@[simp]
theorem uIcc_of_ge (h : b ≤ a) : [a, b] = Icc b a := by rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]
#align set.uIcc_of_ge Set.uIcc_of_ge
-/

#print Set.uIcc_comm /-
theorem uIcc_comm (a b : α) : [a, b] = [b, a] := by simp_rw [uIcc, inf_comm, sup_comm]
#align set.uIcc_comm Set.uIcc_comm
-/

#print Set.uIcc_of_lt /-
theorem uIcc_of_lt (h : a < b) : [a, b] = Icc a b :=
  uIcc_of_le h.le
#align set.uIcc_of_lt Set.uIcc_of_lt
-/

#print Set.uIcc_of_gt /-
theorem uIcc_of_gt (h : b < a) : [a, b] = Icc b a :=
  uIcc_of_ge h.le
#align set.uIcc_of_gt Set.uIcc_of_gt
-/

#print Set.uIcc_self /-
@[simp]
theorem uIcc_self : [a, a] = {a} := by simp [uIcc]
#align set.uIcc_self Set.uIcc_self
-/

#print Set.nonempty_uIcc /-
@[simp]
theorem nonempty_uIcc : [a, b].Nonempty :=
  nonempty_Icc.2 inf_le_sup
#align set.nonempty_uIcc Set.nonempty_uIcc
-/

#print Set.Icc_subset_uIcc /-
theorem Icc_subset_uIcc : Icc a b ⊆ [a, b] :=
  Icc_subset_Icc inf_le_left le_sup_right
#align set.Icc_subset_uIcc Set.Icc_subset_uIcc
-/

#print Set.Icc_subset_uIcc' /-
theorem Icc_subset_uIcc' : Icc b a ⊆ [a, b] :=
  Icc_subset_Icc inf_le_right le_sup_left
#align set.Icc_subset_uIcc' Set.Icc_subset_uIcc'
-/

#print Set.left_mem_uIcc /-
@[simp]
theorem left_mem_uIcc : a ∈ [a, b] :=
  ⟨inf_le_left, le_sup_left⟩
#align set.left_mem_uIcc Set.left_mem_uIcc
-/

#print Set.right_mem_uIcc /-
@[simp]
theorem right_mem_uIcc : b ∈ [a, b] :=
  ⟨inf_le_right, le_sup_right⟩
#align set.right_mem_uIcc Set.right_mem_uIcc
-/

#print Set.mem_uIcc_of_le /-
theorem mem_uIcc_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [a, b] :=
  Icc_subset_uIcc ⟨ha, hb⟩
#align set.mem_uIcc_of_le Set.mem_uIcc_of_le
-/

#print Set.mem_uIcc_of_ge /-
theorem mem_uIcc_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [a, b] :=
  Icc_subset_uIcc' ⟨hb, ha⟩
#align set.mem_uIcc_of_ge Set.mem_uIcc_of_ge
-/

#print Set.uIcc_subset_uIcc /-
theorem uIcc_subset_uIcc (h₁ : a₁ ∈ [a₂, b₂]) (h₂ : b₁ ∈ [a₂, b₂]) : [a₁, b₁] ⊆ [a₂, b₂] :=
  Icc_subset_Icc (le_inf h₁.1 h₂.1) (sup_le h₁.2 h₂.2)
#align set.uIcc_subset_uIcc Set.uIcc_subset_uIcc
-/

#print Set.uIcc_subset_Icc /-
theorem uIcc_subset_Icc (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) : [a₁, b₁] ⊆ Icc a₂ b₂ :=
  Icc_subset_Icc (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)
#align set.uIcc_subset_Icc Set.uIcc_subset_Icc
-/

#print Set.uIcc_subset_uIcc_iff_mem /-
theorem uIcc_subset_uIcc_iff_mem : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₁ ∈ [a₂, b₂] ∧ b₁ ∈ [a₂, b₂] :=
  Iff.intro (fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩) fun h => uIcc_subset_uIcc h.1 h.2
#align set.uIcc_subset_uIcc_iff_mem Set.uIcc_subset_uIcc_iff_mem
-/

#print Set.uIcc_subset_uIcc_iff_le' /-
theorem uIcc_subset_uIcc_iff_le' : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₂ ⊓ b₂ ≤ a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ ≤ a₂ ⊔ b₂ :=
  Icc_subset_Icc_iff inf_le_sup
#align set.uIcc_subset_uIcc_iff_le' Set.uIcc_subset_uIcc_iff_le'
-/

#print Set.uIcc_subset_uIcc_right /-
theorem uIcc_subset_uIcc_right (h : x ∈ [a, b]) : [x, b] ⊆ [a, b] :=
  uIcc_subset_uIcc h right_mem_uIcc
#align set.uIcc_subset_uIcc_right Set.uIcc_subset_uIcc_right
-/

#print Set.uIcc_subset_uIcc_left /-
theorem uIcc_subset_uIcc_left (h : x ∈ [a, b]) : [a, x] ⊆ [a, b] :=
  uIcc_subset_uIcc left_mem_uIcc h
#align set.uIcc_subset_uIcc_left Set.uIcc_subset_uIcc_left
-/

#print Set.bdd_below_bdd_above_iff_subset_uIcc /-
theorem bdd_below_bdd_above_iff_subset_uIcc (s : Set α) :
    BddBelow s ∧ BddAbove s ↔ ∃ a b, s ⊆ [a, b] :=
  bddBelow_bddAbove_iff_subset_Icc.trans
    ⟨fun ⟨a, b, h⟩ => ⟨a, b, fun x hx => Icc_subset_uIcc (h hx)⟩, fun ⟨a, b, h⟩ => ⟨_, _, h⟩⟩
#align set.bdd_below_bdd_above_iff_subset_uIcc Set.bdd_below_bdd_above_iff_subset_uIcc
-/

end Lattice

open Interval

section DistribLattice

variable [DistribLattice α] {a a₁ a₂ b b₁ b₂ c x : α}

#print Set.eq_of_mem_uIcc_of_mem_uIcc /-
theorem eq_of_mem_uIcc_of_mem_uIcc (ha : a ∈ [b, c]) (hb : b ∈ [a, c]) : a = b :=
  eq_of_inf_eq_sup_eq (inf_congr_right ha.1 hb.1) <| sup_congr_right ha.2 hb.2
#align set.eq_of_mem_uIcc_of_mem_uIcc Set.eq_of_mem_uIcc_of_mem_uIcc
-/

#print Set.eq_of_mem_uIcc_of_mem_uIcc' /-
theorem eq_of_mem_uIcc_of_mem_uIcc' : b ∈ [a, c] → c ∈ [a, b] → b = c := by
  simpa only [uIcc_comm a] using eq_of_mem_uIcc_of_mem_uIcc
#align set.eq_of_mem_uIcc_of_mem_uIcc' Set.eq_of_mem_uIcc_of_mem_uIcc'
-/

#print Set.uIcc_injective_right /-
theorem uIcc_injective_right (a : α) : Injective fun b => uIcc b a := fun b c h =>
  by
  rw [ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)
#align set.uIcc_injective_right Set.uIcc_injective_right
-/

#print Set.uIcc_injective_left /-
theorem uIcc_injective_left (a : α) : Injective (uIcc a) := by
  simpa only [uIcc_comm] using uIcc_injective_right a
#align set.uIcc_injective_left Set.uIcc_injective_left
-/

end DistribLattice

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : α → β} {s : Set α} {a a₁ a₂ b b₁ b₂ c d x : α}

/- warning: set.Icc_min_max -> Set.Icc_min_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (LinearOrder.min.{u1} α _inst_1 a b) (LinearOrder.max.{u1} α _inst_1 a b)) (Set.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b)) (Set.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align set.Icc_min_max Set.Icc_min_maxₓ'. -/
theorem Icc_min_max : Icc (min a b) (max a b) = [a, b] :=
  rfl
#align set.Icc_min_max Set.Icc_min_max

#print Set.uIcc_of_not_le /-
theorem uIcc_of_not_le (h : ¬a ≤ b) : [a, b] = Icc b a :=
  uIcc_of_gt <| lt_of_not_ge h
#align set.uIcc_of_not_le Set.uIcc_of_not_le
-/

#print Set.uIcc_of_not_ge /-
theorem uIcc_of_not_ge (h : ¬b ≤ a) : [a, b] = Icc a b :=
  uIcc_of_lt <| lt_of_not_ge h
#align set.uIcc_of_not_ge Set.uIcc_of_not_ge
-/

/- warning: set.uIcc_eq_union -> Set.uIcc_eq_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) a b) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) a b) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) a b) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) b a))
Case conversion may be inaccurate. Consider using '#align set.uIcc_eq_union Set.uIcc_eq_unionₓ'. -/
theorem uIcc_eq_union : [a, b] = Icc a b ∪ Icc b a := by rw [Icc_union_Icc', max_comm] <;> rfl
#align set.uIcc_eq_union Set.uIcc_eq_union

#print Set.mem_uIcc /-
theorem mem_uIcc : a ∈ [b, c] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [uIcc_eq_union]
#align set.mem_uIcc Set.mem_uIcc
-/

#print Set.not_mem_uIcc_of_lt /-
theorem not_mem_uIcc_of_lt (ha : c < a) (hb : c < b) : c ∉ [a, b] :=
  not_mem_Icc_of_lt <| lt_min_iff.mpr ⟨ha, hb⟩
#align set.not_mem_uIcc_of_lt Set.not_mem_uIcc_of_lt
-/

#print Set.not_mem_uIcc_of_gt /-
theorem not_mem_uIcc_of_gt (ha : a < c) (hb : b < c) : c ∉ [a, b] :=
  not_mem_Icc_of_gt <| max_lt_iff.mpr ⟨ha, hb⟩
#align set.not_mem_uIcc_of_gt Set.not_mem_uIcc_of_gt
-/

/- warning: set.uIcc_subset_uIcc_iff_le -> Set.uIcc_subset_uIcc_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) a₁ b₁) (Set.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) a₂ b₂)) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.min.{u1} α _inst_1 a₂ b₂) (LinearOrder.min.{u1} α _inst_1 a₁ b₁)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.max.{u1} α _inst_1 a₁ b₁) (LinearOrder.max.{u1} α _inst_1 a₂ b₂)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) a₁ b₁) (Set.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) a₂ b₂)) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a₂ b₂) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a₁ b₁)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a₁ b₁) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a₂ b₂)))
Case conversion may be inaccurate. Consider using '#align set.uIcc_subset_uIcc_iff_le Set.uIcc_subset_uIcc_iff_leₓ'. -/
theorem uIcc_subset_uIcc_iff_le :
    [a₁, b₁] ⊆ [a₂, b₂] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
  uIcc_subset_uIcc_iff_le'
#align set.uIcc_subset_uIcc_iff_le Set.uIcc_subset_uIcc_iff_le

/- warning: set.uIcc_subset_uIcc_union_uIcc -> Set.uIcc_subset_uIcc_union_uIcc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) a c) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) a b) (Set.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) a c) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Set.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) a b) (Set.uIcc.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)) b c))
Case conversion may be inaccurate. Consider using '#align set.uIcc_subset_uIcc_union_uIcc Set.uIcc_subset_uIcc_union_uIccₓ'. -/
/-- A sort of triangle inequality. -/
theorem uIcc_subset_uIcc_union_uIcc : [a, c] ⊆ [a, b] ∪ [b, c] := fun x => by
  simp only [mem_uIcc, mem_union] <;> cases le_total a c <;> cases le_total x b <;> tauto
#align set.uIcc_subset_uIcc_union_uIcc Set.uIcc_subset_uIcc_union_uIcc

/- warning: set.monotone_or_antitone_iff_uIcc -> Set.monotone_or_antitone_iff_uIcc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β}, Iff (Or (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f) (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f)) (forall (a : α) (b : α) (c : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c (Set.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) a b)) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f c) (Set.uIcc.{u2} β (LinearOrder.toLattice.{u2} β _inst_2) (f a) (f b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u1} β] {f : α -> β}, Iff (Or (Monotone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f) (Antitone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f)) (forall (a : α) (b : α) (c : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c (Set.uIcc.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)) a b)) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f c) (Set.uIcc.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2)) (f a) (f b))))
Case conversion may be inaccurate. Consider using '#align set.monotone_or_antitone_iff_uIcc Set.monotone_or_antitone_iff_uIccₓ'. -/
theorem monotone_or_antitone_iff_uIcc :
    Monotone f ∨ Antitone f ↔ ∀ a b c, c ∈ [a, b] → f c ∈ [f a, f b] :=
  by
  constructor
  · rintro (hf | hf) a b c <;> simp_rw [← Icc_min_max, ← hf.map_min, ← hf.map_max]
    exacts[fun hc => ⟨hf hc.1, hf hc.2⟩, fun hc => ⟨hf hc.2, hf hc.1⟩]
  contrapose!
  rw [not_monotone_not_antitone_iff_exists_le_le]
  rintro ⟨a, b, c, hab, hbc, ⟨hfab, hfcb⟩ | ⟨hfba, hfbc⟩⟩
  · exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.2.not_lt <| max_lt hfab hfcb⟩
  · exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.1.not_lt <| lt_min hfba hfbc⟩
#align set.monotone_or_antitone_iff_uIcc Set.monotone_or_antitone_iff_uIcc

/- warning: set.monotone_on_or_antitone_on_iff_uIcc -> Set.monotoneOn_or_antitoneOn_iff_uIcc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (Or (MonotoneOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f s) (AntitoneOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f s)) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (forall (c : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c (Set.uIcc.{u1} α (LinearOrder.toLattice.{u1} α _inst_1) a b)) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f c) (Set.uIcc.{u2} β (LinearOrder.toLattice.{u2} β _inst_2) (f a) (f b))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u1} β] {f : α -> β} {s : Set.{u2} α}, Iff (Or (MonotoneOn.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f s) (AntitoneOn.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f s)) (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (forall (b : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) b s) -> (forall (c : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c (Set.uIcc.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)) a b)) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f c) (Set.uIcc.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2)) (f a) (f b))))))
Case conversion may be inaccurate. Consider using '#align set.monotone_on_or_antitone_on_iff_uIcc Set.monotoneOn_or_antitoneOn_iff_uIccₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a b c «expr ∈ » s) -/
theorem monotoneOn_or_antitoneOn_iff_uIcc :
    MonotoneOn f s ∨ AntitoneOn f s ↔
      ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s) (c) (_ : c ∈ s), c ∈ [a, b] → f c ∈ [f a, f b] :=
  by
  simp [monotone_on_iff_monotone, antitone_on_iff_antitone, monotone_or_antitone_iff_uIcc, mem_uIcc]
#align set.monotone_on_or_antitone_on_iff_uIcc Set.monotoneOn_or_antitoneOn_iff_uIcc

#print Set.uIoc /-
/-- The open-closed interval with unordered bounds. -/
def uIoc : α → α → Set α := fun a b => Ioc (min a b) (max a b)
#align set.uIoc Set.uIoc
-/

-- mathport name: exprΙ
-- Below is a capital iota
scoped[Interval] notation "Ι" => Set.uIoc

#print Set.uIoc_of_le /-
@[simp]
theorem uIoc_of_le (h : a ≤ b) : Ι a b = Ioc a b := by simp [uIoc, h]
#align set.uIoc_of_le Set.uIoc_of_le
-/

#print Set.uIoc_of_lt /-
@[simp]
theorem uIoc_of_lt (h : b < a) : Ι a b = Ioc b a := by simp [uIoc, h.le]
#align set.uIoc_of_lt Set.uIoc_of_lt
-/

/- warning: set.uIoc_eq_union -> Set.uIoc_eq_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.uIoc.{u1} α _inst_1 a b) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.uIoc.{u1} α _inst_1 a b) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) a b) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) b a))
Case conversion may be inaccurate. Consider using '#align set.uIoc_eq_union Set.uIoc_eq_unionₓ'. -/
theorem uIoc_eq_union : Ι a b = Ioc a b ∪ Ioc b a := by cases le_total a b <;> simp [uIoc, *]
#align set.uIoc_eq_union Set.uIoc_eq_union

#print Set.mem_uIoc /-
theorem mem_uIoc : a ∈ Ι b c ↔ b < a ∧ a ≤ c ∨ c < a ∧ a ≤ b := by
  simp only [uIoc_eq_union, mem_union, mem_Ioc]
#align set.mem_uIoc Set.mem_uIoc
-/

#print Set.not_mem_uIoc /-
theorem not_mem_uIoc : a ∉ Ι b c ↔ a ≤ b ∧ a ≤ c ∨ c < a ∧ b < a :=
  by
  simp only [uIoc_eq_union, mem_union, mem_Ioc, not_lt, ← not_le]
  tauto
#align set.not_mem_uIoc Set.not_mem_uIoc
-/

#print Set.left_mem_uIoc /-
@[simp]
theorem left_mem_uIoc : a ∈ Ι a b ↔ b < a := by simp [mem_uIoc]
#align set.left_mem_uIoc Set.left_mem_uIoc
-/

#print Set.right_mem_uIoc /-
@[simp]
theorem right_mem_uIoc : b ∈ Ι a b ↔ a < b := by simp [mem_uIoc]
#align set.right_mem_uIoc Set.right_mem_uIoc
-/

#print Set.forall_uIoc_iff /-
theorem forall_uIoc_iff {P : α → Prop} :
    (∀ x ∈ Ι a b, P x) ↔ (∀ x ∈ Ioc a b, P x) ∧ ∀ x ∈ Ioc b a, P x := by
  simp only [uIoc_eq_union, mem_union, or_imp, forall_and]
#align set.forall_uIoc_iff Set.forall_uIoc_iff
-/

#print Set.uIoc_subset_uIoc_of_uIcc_subset_uIcc /-
theorem uIoc_subset_uIoc_of_uIcc_subset_uIcc (h : [a, b] ⊆ [c, d]) : Ι a b ⊆ Ι c d :=
  Ioc_subset_Ioc (uIcc_subset_uIcc_iff_le.1 h).1 (uIcc_subset_uIcc_iff_le.1 h).2
#align set.uIoc_subset_uIoc_of_uIcc_subset_uIcc Set.uIoc_subset_uIoc_of_uIcc_subset_uIcc
-/

theorem uIoc_swap (a b : α) : Ι a b = Ι b a := by simp only [uIoc, min_comm a b, max_comm a b]
#align set.uIoc_swap Set.uIoc_swap

#print Set.Ioc_subset_uIoc /-
theorem Ioc_subset_uIoc : Ioc a b ⊆ Ι a b :=
  Ioc_subset_Ioc (min_le_left _ _) (le_max_right _ _)
#align set.Ioc_subset_uIoc Set.Ioc_subset_uIoc
-/

#print Set.Ioc_subset_uIoc' /-
theorem Ioc_subset_uIoc' : Ioc a b ⊆ Ι b a :=
  Ioc_subset_Ioc (min_le_right _ _) (le_max_left _ _)
#align set.Ioc_subset_uIoc' Set.Ioc_subset_uIoc'
-/

#print Set.eq_of_mem_uIoc_of_mem_uIoc /-
theorem eq_of_mem_uIoc_of_mem_uIoc : a ∈ Ι b c → b ∈ Ι a c → a = b := by
  simp_rw [mem_uIoc] <;> rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩) <;> apply le_antisymm <;>
    first |assumption|exact le_of_lt ‹_›|exact le_trans ‹_› (le_of_lt ‹_›)
#align set.eq_of_mem_uIoc_of_mem_uIoc Set.eq_of_mem_uIoc_of_mem_uIoc
-/

#print Set.eq_of_mem_uIoc_of_mem_uIoc' /-
theorem eq_of_mem_uIoc_of_mem_uIoc' : b ∈ Ι a c → c ∈ Ι a b → b = c := by
  simpa only [uIoc_swap a] using eq_of_mem_uIoc_of_mem_uIoc
#align set.eq_of_mem_uIoc_of_mem_uIoc' Set.eq_of_mem_uIoc_of_mem_uIoc'
-/

#print Set.eq_of_not_mem_uIoc_of_not_mem_uIoc /-
theorem eq_of_not_mem_uIoc_of_not_mem_uIoc (ha : a ≤ c) (hb : b ≤ c) :
    a ∉ Ι b c → b ∉ Ι a c → a = b := by
  simp_rw [not_mem_uIoc] <;> rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩) <;> apply le_antisymm <;>
    first |assumption|exact le_of_lt ‹_›|cases not_le_of_lt ‹_› ‹_›
#align set.eq_of_not_mem_uIoc_of_not_mem_uIoc Set.eq_of_not_mem_uIoc_of_not_mem_uIoc
-/

#print Set.uIoc_injective_right /-
theorem uIoc_injective_right (a : α) : Injective fun b => Ι b a :=
  by
  rintro b c h
  rw [ext_iff] at h
  obtain ha | ha := le_or_lt b a
  · have hb := (h b).Not
    simp only [ha, left_mem_uIoc, not_lt, true_iff_iff, not_mem_uIoc, ← not_le, and_true_iff,
      not_true, false_and_iff, not_false_iff, true_iff_iff, or_false_iff] at hb
    refine' hb.eq_of_not_lt fun hc => _
    simpa [ha, and_iff_right hc, ← @not_le _ _ _ a, -not_le] using h c
  · refine'
      eq_of_mem_uIoc_of_mem_uIoc ((h _).1 <| left_mem_uIoc.2 ha)
        ((h _).2 <| left_mem_uIoc.2 <| ha.trans_le _)
    simpa [ha, ha.not_le, mem_uIoc] using h b
#align set.uIoc_injective_right Set.uIoc_injective_right
-/

#print Set.uIoc_injective_left /-
theorem uIoc_injective_left (a : α) : Injective (Ι a) := by
  simpa only [uIoc_swap] using uIoc_injective_right a
#align set.uIoc_injective_left Set.uIoc_injective_left
-/

end LinearOrder

end Set

