/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module data.set.intervals.surj_on
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Intervals.Basic
import Mathbin.Data.Set.Function

/-!
# Monotone surjective functions are surjective on intervals

A monotone surjective function sends any interval in the domain onto the interval with corresponding
endpoints in the range.  This is expressed in this file using `set.surj_on`, and provided for all
permutations of interval endpoints.
-/


variable {α : Type _} {β : Type _} [LinearOrder α] [PartialOrder β] {f : α → β}

open Set Function

open OrderDual (toDual)

/- warning: surj_on_Ioo_of_monotone_surjective -> surjOn_Ioo_of_monotone_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β _inst_2) f) -> (Function.Surjective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Set.SurjOn.{u1, u2} α β f (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b) (Set.Ioo.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) (f a) (f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β _inst_2) f) -> (Function.Surjective.{succ u2, succ u1} α β f) -> (forall (a : α) (b : α), Set.SurjOn.{u2, u1} α β f (Set.Ioo.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a b) (Set.Ioo.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align surj_on_Ioo_of_monotone_surjective surjOn_Ioo_of_monotone_surjectiveₓ'. -/
theorem surjOn_Ioo_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ioo a b) (Ioo (f a) (f b)) := by
  intro p hp
  rcases h_surj p with ⟨x, rfl⟩
  refine' ⟨x, mem_Ioo.2 _, rfl⟩
  contrapose! hp
  exact fun h => h.2.not_le (h_mono <| hp <| h_mono.reflect_lt h.1)
#align surj_on_Ioo_of_monotone_surjective surjOn_Ioo_of_monotone_surjective

/- warning: surj_on_Ico_of_monotone_surjective -> surjOn_Ico_of_monotone_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β _inst_2) f) -> (Function.Surjective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Set.SurjOn.{u1, u2} α β f (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b) (Set.Ico.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) (f a) (f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β _inst_2) f) -> (Function.Surjective.{succ u2, succ u1} α β f) -> (forall (a : α) (b : α), Set.SurjOn.{u2, u1} α β f (Set.Ico.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a b) (Set.Ico.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align surj_on_Ico_of_monotone_surjective surjOn_Ico_of_monotone_surjectiveₓ'. -/
theorem surjOn_Ico_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ico a b) (Ico (f a) (f b)) := by
  obtain hab | hab := lt_or_le a b
  · intro p hp
    rcases eq_left_or_mem_Ioo_of_mem_Ico hp with (rfl | hp')
    · exact mem_image_of_mem f (left_mem_Ico.mpr hab)
    · have := surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'
      exact image_subset f Ioo_subset_Ico_self this
  · rw [Ico_eq_empty (h_mono hab).not_lt]
    exact surj_on_empty f _
#align surj_on_Ico_of_monotone_surjective surjOn_Ico_of_monotone_surjective

/- warning: surj_on_Ioc_of_monotone_surjective -> surjOn_Ioc_of_monotone_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β _inst_2) f) -> (Function.Surjective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Set.SurjOn.{u1, u2} α β f (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b) (Set.Ioc.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) (f a) (f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β _inst_2) f) -> (Function.Surjective.{succ u2, succ u1} α β f) -> (forall (a : α) (b : α), Set.SurjOn.{u2, u1} α β f (Set.Ioc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a b) (Set.Ioc.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align surj_on_Ioc_of_monotone_surjective surjOn_Ioc_of_monotone_surjectiveₓ'. -/
theorem surjOn_Ioc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ioc a b) (Ioc (f a) (f b)) := by
  simpa using surjOn_Ico_of_monotone_surjective h_mono.dual h_surj (to_dual b) (to_dual a)
#align surj_on_Ioc_of_monotone_surjective surjOn_Ioc_of_monotone_surjective

/- warning: surj_on_Icc_of_monotone_surjective -> surjOn_Icc_of_monotone_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β _inst_2) f) -> (Function.Surjective.{succ u1, succ u2} α β f) -> (forall {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b) -> (Set.SurjOn.{u1, u2} α β f (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b) (Set.Icc.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) (f a) (f b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β _inst_2) f) -> (Function.Surjective.{succ u2, succ u1} α β f) -> (forall {a : α} {b : α}, (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a b) -> (Set.SurjOn.{u2, u1} α β f (Set.Icc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a b) (Set.Icc.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) (f a) (f b))))
Case conversion may be inaccurate. Consider using '#align surj_on_Icc_of_monotone_surjective surjOn_Icc_of_monotone_surjectiveₓ'. -/
-- to see that the hypothesis `a ≤ b` is necessary, consider a constant function
theorem surjOn_Icc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    {a b : α} (hab : a ≤ b) : SurjOn f (Icc a b) (Icc (f a) (f b)) := by
  intro p hp
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hp with (rfl | rfl | hp')
  · exact ⟨a, left_mem_Icc.mpr hab, rfl⟩
  · exact ⟨b, right_mem_Icc.mpr hab, rfl⟩
  · have := surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'
    exact image_subset f Ioo_subset_Icc_self this
#align surj_on_Icc_of_monotone_surjective surjOn_Icc_of_monotone_surjective

/- warning: surj_on_Ioi_of_monotone_surjective -> surjOn_Ioi_of_monotone_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β _inst_2) f) -> (Function.Surjective.{succ u1, succ u2} α β f) -> (forall (a : α), Set.SurjOn.{u1, u2} α β f (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a) (Set.Ioi.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β _inst_2) f) -> (Function.Surjective.{succ u2, succ u1} α β f) -> (forall (a : α), Set.SurjOn.{u2, u1} α β f (Set.Ioi.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a) (Set.Ioi.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) (f a)))
Case conversion may be inaccurate. Consider using '#align surj_on_Ioi_of_monotone_surjective surjOn_Ioi_of_monotone_surjectiveₓ'. -/
theorem surjOn_Ioi_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Ioi a) (Ioi (f a)) := by
  rw [← compl_Iic, ← compl_compl (Ioi (f a))]
  refine' maps_to.surj_on_compl _ h_surj
  exact fun x hx => (h_mono hx).not_lt
#align surj_on_Ioi_of_monotone_surjective surjOn_Ioi_of_monotone_surjective

/- warning: surj_on_Iio_of_monotone_surjective -> surjOn_Iio_of_monotone_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β _inst_2) f) -> (Function.Surjective.{succ u1, succ u2} α β f) -> (forall (a : α), Set.SurjOn.{u1, u2} α β f (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a) (Set.Iio.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β _inst_2) f) -> (Function.Surjective.{succ u2, succ u1} α β f) -> (forall (a : α), Set.SurjOn.{u2, u1} α β f (Set.Iio.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a) (Set.Iio.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) (f a)))
Case conversion may be inaccurate. Consider using '#align surj_on_Iio_of_monotone_surjective surjOn_Iio_of_monotone_surjectiveₓ'. -/
theorem surjOn_Iio_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Iio a) (Iio (f a)) :=
  @surjOn_Ioi_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a
#align surj_on_Iio_of_monotone_surjective surjOn_Iio_of_monotone_surjective

/- warning: surj_on_Ici_of_monotone_surjective -> surjOn_Ici_of_monotone_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β _inst_2) f) -> (Function.Surjective.{succ u1, succ u2} α β f) -> (forall (a : α), Set.SurjOn.{u1, u2} α β f (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a) (Set.Ici.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β _inst_2) f) -> (Function.Surjective.{succ u2, succ u1} α β f) -> (forall (a : α), Set.SurjOn.{u2, u1} α β f (Set.Ici.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a) (Set.Ici.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) (f a)))
Case conversion may be inaccurate. Consider using '#align surj_on_Ici_of_monotone_surjective surjOn_Ici_of_monotone_surjectiveₓ'. -/
theorem surjOn_Ici_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Ici a) (Ici (f a)) := by
  rw [← Ioi_union_left, ← Ioi_union_left]
  exact
    (surjOn_Ioi_of_monotone_surjective h_mono h_surj a).union_union
      (@image_singleton _ _ f a ▸ surj_on_image _ _)
#align surj_on_Ici_of_monotone_surjective surjOn_Ici_of_monotone_surjective

/- warning: surj_on_Iic_of_monotone_surjective -> surjOn_Iic_of_monotone_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β _inst_2) f) -> (Function.Surjective.{succ u1, succ u2} α β f) -> (forall (a : α), Set.SurjOn.{u1, u2} α β f (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a) (Set.Iic.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β _inst_2) f) -> (Function.Surjective.{succ u2, succ u1} α β f) -> (forall (a : α), Set.SurjOn.{u2, u1} α β f (Set.Iic.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a) (Set.Iic.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) (f a)))
Case conversion may be inaccurate. Consider using '#align surj_on_Iic_of_monotone_surjective surjOn_Iic_of_monotone_surjectiveₓ'. -/
theorem surjOn_Iic_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Iic a) (Iic (f a)) :=
  @surjOn_Ici_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a
#align surj_on_Iic_of_monotone_surjective surjOn_Iic_of_monotone_surjective

