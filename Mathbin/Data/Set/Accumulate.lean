/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module data.set.accumulate
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Lattice

/-!
# Accumulate

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The function `accumulate` takes a set `s` and returns `⋃ y ≤ x, s y`.
-/


variable {α β γ : Type _} {s : α → Set β} {t : α → Set γ}

namespace Set

#print Set.Accumulate /-
/-- `accumulate s` is the union of `s y` for `y ≤ x`. -/
def Accumulate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋃ y ≤ x, s y
#align set.accumulate Set.Accumulate
-/

variable {s}

/- warning: set.accumulate_def -> Set.accumulate_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : α -> (Set.{u2} β)} [_inst_1 : LE.{u1} α] {x : α}, Eq.{succ u2} (Set.{u2} β) (Set.Accumulate.{u1, u2} α β _inst_1 s x) (Set.unionᵢ.{u2, succ u1} β α (fun (y : α) => Set.unionᵢ.{u2, 0} β (LE.le.{u1} α _inst_1 y x) (fun (H : LE.le.{u1} α _inst_1 y x) => s y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : α -> (Set.{u1} β)} [_inst_1 : LE.{u2} α] {x : α}, Eq.{succ u1} (Set.{u1} β) (Set.Accumulate.{u2, u1} α β _inst_1 s x) (Set.unionᵢ.{u1, succ u2} β α (fun (y : α) => Set.unionᵢ.{u1, 0} β (LE.le.{u2} α _inst_1 y x) (fun (H : LE.le.{u2} α _inst_1 y x) => s y)))
Case conversion may be inaccurate. Consider using '#align set.accumulate_def Set.accumulate_defₓ'. -/
theorem accumulate_def [LE α] {x : α} : Accumulate s x = ⋃ y ≤ x, s y :=
  rfl
#align set.accumulate_def Set.accumulate_def

/- warning: set.mem_accumulate -> Set.mem_accumulate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : α -> (Set.{u2} β)} [_inst_1 : LE.{u1} α] {x : α} {z : β}, Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) z (Set.Accumulate.{u1, u2} α β _inst_1 s x)) (Exists.{succ u1} α (fun (y : α) => Exists.{0} (LE.le.{u1} α _inst_1 y x) (fun (H : LE.le.{u1} α _inst_1 y x) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) z (s y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : α -> (Set.{u1} β)} [_inst_1 : LE.{u2} α] {x : α} {z : β}, Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) z (Set.Accumulate.{u2, u1} α β _inst_1 s x)) (Exists.{succ u2} α (fun (y : α) => And (LE.le.{u2} α _inst_1 y x) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) z (s y))))
Case conversion may be inaccurate. Consider using '#align set.mem_accumulate Set.mem_accumulateₓ'. -/
@[simp]
theorem mem_accumulate [LE α] {x : α} {z : β} : z ∈ Accumulate s x ↔ ∃ y ≤ x, z ∈ s y :=
  mem_unionᵢ₂
#align set.mem_accumulate Set.mem_accumulate

/- warning: set.subset_accumulate -> Set.subset_accumulate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : α -> (Set.{u2} β)} [_inst_1 : Preorder.{u1} α] {x : α}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (s x) (Set.Accumulate.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) s x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : α -> (Set.{u1} β)} [_inst_1 : Preorder.{u2} α] {x : α}, HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (s x) (Set.Accumulate.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) s x)
Case conversion may be inaccurate. Consider using '#align set.subset_accumulate Set.subset_accumulateₓ'. -/
theorem subset_accumulate [Preorder α] {x : α} : s x ⊆ Accumulate s x := fun z => mem_bunionᵢ le_rfl
#align set.subset_accumulate Set.subset_accumulate

/- warning: set.monotone_accumulate -> Set.monotone_accumulate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : α -> (Set.{u2} β)} [_inst_1 : Preorder.{u1} α], Monotone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (Set.Accumulate.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : α -> (Set.{u1} β)} [_inst_1 : Preorder.{u2} α], Monotone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (Set.Accumulate.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align set.monotone_accumulate Set.monotone_accumulateₓ'. -/
theorem monotone_accumulate [Preorder α] : Monotone (Accumulate s) := fun x y hxy =>
  bunionᵢ_subset_bunionᵢ_left fun z hz => le_trans hz hxy
#align set.monotone_accumulate Set.monotone_accumulate

/- warning: set.bUnion_accumulate -> Set.bunionᵢ_accumulate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : α -> (Set.{u2} β)} [_inst_1 : Preorder.{u1} α] (x : α), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (y : α) => Set.unionᵢ.{u2, 0} β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) y x) (fun (H : LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) y x) => Set.Accumulate.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) s y))) (Set.unionᵢ.{u2, succ u1} β α (fun (y : α) => Set.unionᵢ.{u2, 0} β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) y x) (fun (H : LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) y x) => s y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : α -> (Set.{u1} β)} [_inst_1 : Preorder.{u2} α] (x : α), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (y : α) => Set.unionᵢ.{u1, 0} β (LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) y x) (fun (H : LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) y x) => Set.Accumulate.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) s y))) (Set.unionᵢ.{u1, succ u2} β α (fun (y : α) => Set.unionᵢ.{u1, 0} β (LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) y x) (fun (H : LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) y x) => s y)))
Case conversion may be inaccurate. Consider using '#align set.bUnion_accumulate Set.bunionᵢ_accumulateₓ'. -/
theorem bunionᵢ_accumulate [Preorder α] (x : α) : (⋃ y ≤ x, Accumulate s y) = ⋃ y ≤ x, s y :=
  by
  apply subset.antisymm
  · exact Union₂_subset fun y hy => monotone_accumulate hy
  · exact Union₂_mono fun y hy => subset_accumulate
#align set.bUnion_accumulate Set.bunionᵢ_accumulate

/- warning: set.Union_accumulate -> Set.unionᵢ_accumulate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : α -> (Set.{u2} β)} [_inst_1 : Preorder.{u1} α], Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.Accumulate.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) s x)) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => s x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : α -> (Set.{u1} β)} [_inst_1 : Preorder.{u2} α], Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.Accumulate.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) s x)) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => s x))
Case conversion may be inaccurate. Consider using '#align set.Union_accumulate Set.unionᵢ_accumulateₓ'. -/
theorem unionᵢ_accumulate [Preorder α] : (⋃ x, Accumulate s x) = ⋃ x, s x :=
  by
  apply subset.antisymm
  · simp only [subset_def, mem_Union, exists_imp, mem_accumulate]
    intro z x x' hx'x hz
    exact ⟨x', hz⟩
  · exact Union_mono fun i => subset_accumulate
#align set.Union_accumulate Set.unionᵢ_accumulate

end Set

