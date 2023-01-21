/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module order.monotone.extension
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic

/-!
# Extension of a monotone function from a set to the whole space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that if a function is monotone and is bounded on a set `s`, then it admits a
monotone extension to the whole space.
-/


open Set

variable {α β : Type _} [LinearOrder α] [ConditionallyCompleteLinearOrder β] {f : α → β} {s : Set α}
  {a b : α}

/- warning: monotone_on.exists_monotone_extension -> MonotoneOn.exists_monotone_extension is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : ConditionallyCompleteLinearOrder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (MonotoneOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_2))))) f s) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_2))))) (Set.image.{u1, u2} α β f s)) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_2))))) (Set.image.{u1, u2} α β f s)) -> (Exists.{max (succ u1) (succ u2)} (α -> β) (fun (g : α -> β) => And (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_2))))) g) (Set.EqOn.{u1, u2} α β f g s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : ConditionallyCompleteLinearOrder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (MonotoneOn.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} β _inst_2))))) f s) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} β _inst_2))))) (Set.image.{u2, u1} α β f s)) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} β _inst_2))))) (Set.image.{u2, u1} α β f s)) -> (Exists.{max (succ u2) (succ u1)} (α -> β) (fun (g : α -> β) => And (Monotone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} β _inst_2))))) g) (Set.EqOn.{u2, u1} α β f g s)))
Case conversion may be inaccurate. Consider using '#align monotone_on.exists_monotone_extension MonotoneOn.exists_monotone_extensionₓ'. -/
/-- If a function is monotone and is bounded on a set `s`, then it admits a monotone extension to
the whole space. -/
theorem MonotoneOn.exists_monotone_extension (h : MonotoneOn f s) (hl : BddBelow (f '' s))
    (hu : BddAbove (f '' s)) : ∃ g : α → β, Monotone g ∧ EqOn f g s := by
  classical
    /- The extension is defined by `f x = f a` for `x ≤ a`, and `f x` is the supremum of the values
      of `f`  to the left of `x` for `x ≥ a`. -/
    rcases hl with ⟨a, ha⟩
    have hu' : ∀ x, BddAbove (f '' (Iic x ∩ s)) := fun x =>
      hu.mono (image_subset _ (inter_subset_right _ _))
    set g : α → β := fun x => if Disjoint (Iic x) s then a else Sup (f '' (Iic x ∩ s))
    have hgs : eq_on f g s := by
      intro x hx
      simp only [g]
      have : IsGreatest (Iic x ∩ s) x := ⟨⟨right_mem_Iic, hx⟩, fun y hy => hy.1⟩
      rw [if_neg this.nonempty.not_disjoint,
        ((h.mono <| inter_subset_right _ _).map_is_greatest this).cSup_eq]
    refine' ⟨g, fun x y hxy => _, hgs⟩
    by_cases hx : Disjoint (Iic x) s <;> by_cases hy : Disjoint (Iic y) s <;>
      simp only [g, if_pos, if_neg, not_false_iff, *]
    · rcases not_disjoint_iff_nonempty_inter.1 hy with ⟨z, hz⟩
      exact le_csupₛ_of_le (hu' _) (mem_image_of_mem _ hz) (ha <| mem_image_of_mem _ hz.2)
    · exact (hx <| hy.mono_left <| Iic_subset_Iic.2 hxy).elim
    · rw [not_disjoint_iff_nonempty_inter] at hx hy
      refine' csupₛ_le_csupₛ (hu' _) (hx.image _) (image_subset _ _)
      exact inter_subset_inter_left _ (Iic_subset_Iic.2 hxy)
#align monotone_on.exists_monotone_extension MonotoneOn.exists_monotone_extension

/- warning: antitone_on.exists_antitone_extension -> AntitoneOn.exists_antitone_extension is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : ConditionallyCompleteLinearOrder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (AntitoneOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_2))))) f s) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_2))))) (Set.image.{u1, u2} α β f s)) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_2))))) (Set.image.{u1, u2} α β f s)) -> (Exists.{max (succ u1) (succ u2)} (α -> β) (fun (g : α -> β) => And (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_2))))) g) (Set.EqOn.{u1, u2} α β f g s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : ConditionallyCompleteLinearOrder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (AntitoneOn.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} β _inst_2))))) f s) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} β _inst_2))))) (Set.image.{u2, u1} α β f s)) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} β _inst_2))))) (Set.image.{u2, u1} α β f s)) -> (Exists.{max (succ u2) (succ u1)} (α -> β) (fun (g : α -> β) => And (Antitone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} β _inst_2))))) g) (Set.EqOn.{u2, u1} α β f g s)))
Case conversion may be inaccurate. Consider using '#align antitone_on.exists_antitone_extension AntitoneOn.exists_antitone_extensionₓ'. -/
/-- If a function is antitone and is bounded on a set `s`, then it admits an antitone extension to
the whole space. -/
theorem AntitoneOn.exists_antitone_extension (h : AntitoneOn f s) (hl : BddBelow (f '' s))
    (hu : BddAbove (f '' s)) : ∃ g : α → β, Antitone g ∧ EqOn f g s :=
  h.dual_right.exists_monotone_extension hu hl
#align antitone_on.exists_antitone_extension AntitoneOn.exists_antitone_extension

