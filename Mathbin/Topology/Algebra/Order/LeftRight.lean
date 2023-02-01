/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.algebra.order.left_right
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.ContinuousOn

/-!
# Left and right continuity

In this file we prove a few lemmas about left and right continuous functions:

* `continuous_within_at_Ioi_iff_Ici`: two definitions of right continuity
  (with `(a, ∞)` and with `[a, ∞)`) are equivalent;
* `continuous_within_at_Iio_iff_Iic`: two definitions of left continuity
  (with `(-∞, a)` and with `(-∞, a]`) are equivalent;
* `continuous_at_iff_continuous_left_right`, `continuous_at_iff_continuous_left'_right'` :
  a function is continuous at `a` if and only if it is left and right continuous at `a`.

## Tags

left continuous, right continuous
-/


open Set Filter

open Topology

section PartialOrder

variable {α β : Type _} [TopologicalSpace α] [PartialOrder α] [TopologicalSpace β]

/- warning: continuous_within_at_Ioi_iff_Ici -> continuousWithinAt_Ioi_iff_Ici is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] {a : α} {f : α -> β}, Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_3 f (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) a) a) (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_3 f (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) a) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : PartialOrder.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] {a : α} {f : α -> β}, Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_3 f (Set.Ioi.{u2} α (PartialOrder.toPreorder.{u2} α _inst_2) a) a) (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_3 f (Set.Ici.{u2} α (PartialOrder.toPreorder.{u2} α _inst_2) a) a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at_Ioi_iff_Ici continuousWithinAt_Ioi_iff_Iciₓ'. -/
theorem continuousWithinAt_Ioi_iff_Ici {a : α} {f : α → β} :
    ContinuousWithinAt f (Ioi a) a ↔ ContinuousWithinAt f (Ici a) a := by
  simp only [← Ici_diff_left, continuousWithinAt_diff_self]
#align continuous_within_at_Ioi_iff_Ici continuousWithinAt_Ioi_iff_Ici

/- warning: continuous_within_at_Iio_iff_Iic -> continuousWithinAt_Iio_iff_Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] {a : α} {f : α -> β}, Iff (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_3 f (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) a) a) (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_3 f (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) a) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : PartialOrder.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] {a : α} {f : α -> β}, Iff (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_3 f (Set.Iio.{u2} α (PartialOrder.toPreorder.{u2} α _inst_2) a) a) (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_3 f (Set.Iic.{u2} α (PartialOrder.toPreorder.{u2} α _inst_2) a) a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at_Iio_iff_Iic continuousWithinAt_Iio_iff_Iicₓ'. -/
theorem continuousWithinAt_Iio_iff_Iic {a : α} {f : α → β} :
    ContinuousWithinAt f (Iio a) a ↔ ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_Ioi_iff_Ici αᵒᵈ _ ‹TopologicalSpace α› _ _ _ f
#align continuous_within_at_Iio_iff_Iic continuousWithinAt_Iio_iff_Iic

/- warning: nhds_left'_le_nhds_ne -> nhds_left'_le_nhds_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : PartialOrder.{u1} α] (a : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhdsWithin.{u1} α _inst_1 a (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) a)) (nhdsWithin.{u1} α _inst_1 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : PartialOrder.{u1} α] (a : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhdsWithin.{u1} α _inst_1 a (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) a)) (nhdsWithin.{u1} α _inst_1 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)))
Case conversion may be inaccurate. Consider using '#align nhds_left'_le_nhds_ne nhds_left'_le_nhds_neₓ'. -/
theorem nhds_left'_le_nhds_ne (a : α) : 𝓝[<] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono a fun y hy => ne_of_lt hy
#align nhds_left'_le_nhds_ne nhds_left'_le_nhds_ne

/- warning: nhds_right'_le_nhds_ne -> nhds_right'_le_nhds_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : PartialOrder.{u1} α] (a : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhdsWithin.{u1} α _inst_1 a (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) a)) (nhdsWithin.{u1} α _inst_1 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : PartialOrder.{u1} α] (a : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhdsWithin.{u1} α _inst_1 a (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) a)) (nhdsWithin.{u1} α _inst_1 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)))
Case conversion may be inaccurate. Consider using '#align nhds_right'_le_nhds_ne nhds_right'_le_nhds_neₓ'. -/
theorem nhds_right'_le_nhds_ne (a : α) : 𝓝[>] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono a fun y hy => ne_of_gt hy
#align nhds_right'_le_nhds_ne nhds_right'_le_nhds_ne

end PartialOrder

section TopologicalSpace

variable {α β : Type _} [TopologicalSpace α] [LinearOrder α] [TopologicalSpace β]

/- warning: nhds_left_sup_nhds_right -> nhds_left_sup_nhds_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a)) (nhdsWithin.{u1} α _inst_1 a (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a))) (nhds.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2))))) a)) (nhdsWithin.{u1} α _inst_1 a (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2))))) a))) (nhds.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align nhds_left_sup_nhds_right nhds_left_sup_nhds_rightₓ'. -/
theorem nhds_left_sup_nhds_right (a : α) : 𝓝[≤] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ici, nhdsWithin_univ]
#align nhds_left_sup_nhds_right nhds_left_sup_nhds_right

/- warning: nhds_left'_sup_nhds_right -> nhds_left'_sup_nhds_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a)) (nhdsWithin.{u1} α _inst_1 a (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a))) (nhds.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2))))) a)) (nhdsWithin.{u1} α _inst_1 a (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2))))) a))) (nhds.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align nhds_left'_sup_nhds_right nhds_left'_sup_nhds_rightₓ'. -/
theorem nhds_left'_sup_nhds_right (a : α) : 𝓝[<] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iio_union_Ici, nhdsWithin_univ]
#align nhds_left'_sup_nhds_right nhds_left'_sup_nhds_right

/- warning: nhds_left_sup_nhds_right' -> nhds_left_sup_nhds_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a)) (nhdsWithin.{u1} α _inst_1 a (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a))) (nhds.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2))))) a)) (nhdsWithin.{u1} α _inst_1 a (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2))))) a))) (nhds.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align nhds_left_sup_nhds_right' nhds_left_sup_nhds_right'ₓ'. -/
theorem nhds_left_sup_nhds_right' (a : α) : 𝓝[≤] a ⊔ 𝓝[>] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ioi, nhdsWithin_univ]
#align nhds_left_sup_nhds_right' nhds_left_sup_nhds_right'

/- warning: nhds_left'_sup_nhds_right' -> nhds_left'_sup_nhds_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a)) (nhdsWithin.{u1} α _inst_1 a (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a))) (nhdsWithin.{u1} α _inst_1 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))) (nhdsWithin.{u1} α _inst_1 a (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2))))) a)) (nhdsWithin.{u1} α _inst_1 a (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2))))) a))) (nhdsWithin.{u1} α _inst_1 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)))
Case conversion may be inaccurate. Consider using '#align nhds_left'_sup_nhds_right' nhds_left'_sup_nhds_right'ₓ'. -/
theorem nhds_left'_sup_nhds_right' (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[≠] a := by
  rw [← nhdsWithin_union, Iio_union_Ioi]
#align nhds_left'_sup_nhds_right' nhds_left'_sup_nhds_right'

/- warning: continuous_at_iff_continuous_left_right -> continuousAt_iff_continuous_left_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] {a : α} {f : α -> β}, Iff (ContinuousAt.{u1, u2} α β _inst_1 _inst_3 f a) (And (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_3 f (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a) a) (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_3 f (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] {a : α} {f : α -> β}, Iff (ContinuousAt.{u2, u1} α β _inst_1 _inst_3 f a) (And (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_3 f (Set.Iic.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a) a) (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_3 f (Set.Ici.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a) a))
Case conversion may be inaccurate. Consider using '#align continuous_at_iff_continuous_left_right continuousAt_iff_continuous_left_rightₓ'. -/
theorem continuousAt_iff_continuous_left_right {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a ∧ ContinuousWithinAt f (Ici a) a := by
  simp only [ContinuousWithinAt, ContinuousAt, ← tendsto_sup, nhds_left_sup_nhds_right]
#align continuous_at_iff_continuous_left_right continuousAt_iff_continuous_left_right

/- warning: continuous_at_iff_continuous_left'_right' -> continuousAt_iff_continuous_left'_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] {a : α} {f : α -> β}, Iff (ContinuousAt.{u1, u2} α β _inst_1 _inst_3 f a) (And (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_3 f (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a) a) (ContinuousWithinAt.{u1, u2} α β _inst_1 _inst_3 f (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] {a : α} {f : α -> β}, Iff (ContinuousAt.{u2, u1} α β _inst_1 _inst_3 f a) (And (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_3 f (Set.Iio.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a) a) (ContinuousWithinAt.{u2, u1} α β _inst_1 _inst_3 f (Set.Ioi.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a) a))
Case conversion may be inaccurate. Consider using '#align continuous_at_iff_continuous_left'_right' continuousAt_iff_continuous_left'_right'ₓ'. -/
theorem continuousAt_iff_continuous_left'_right' {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iio a) a ∧ ContinuousWithinAt f (Ioi a) a := by
  rw [continuousWithinAt_Ioi_iff_Ici, continuousWithinAt_Iio_iff_Iic,
    continuousAt_iff_continuous_left_right]
#align continuous_at_iff_continuous_left'_right' continuousAt_iff_continuous_left'_right'

end TopologicalSpace

