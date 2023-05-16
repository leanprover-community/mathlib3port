/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.extend_from
! leanprover-community/mathlib commit 3e32bc908f617039c74c06ea9a897e30c30803c2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order.Basic
import Mathbin.Topology.ExtendFrom

/-!
# Lemmas about `extend_from` in an order topology.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Filter Set TopologicalSpace

open Topology Classical

universe u v

variable {α : Type u} {β : Type v}

/- warning: continuous_on_Icc_extend_from_Ioo -> continuousOn_Icc_extendFrom_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))))] [_inst_4 : OrderTopology.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))] [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : RegularSpace.{u2} β _inst_5] {f : α -> β} {a : α} {b : α} {la : β} {lb : β}, (Ne.{succ u1} α a b) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_5 f (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a b)) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a)) (nhds.{u2} β _inst_5 la)) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 b (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) b)) (nhds.{u2} β _inst_5 lb)) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_5 (extendFrom.{u1, u2} α β _inst_1 _inst_5 (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a b) f) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : DenselyOrdered.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))))] [_inst_4 : OrderTopology.{u2} α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2)))))] [_inst_5 : TopologicalSpace.{u1} β] [_inst_6 : RegularSpace.{u1} β _inst_5] {f : α -> β} {a : α} {b : α} {la : β} {lb : β}, (Ne.{succ u2} α a b) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_5 f (Set.Ioo.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a b)) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a (Set.Ioi.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a)) (nhds.{u1} β _inst_5 la)) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 b (Set.Iio.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) b)) (nhds.{u1} β _inst_5 lb)) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_5 (extendFrom.{u2, u1} α β _inst_1 _inst_5 (Set.Ioo.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a b) f) (Set.Icc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a b))
Case conversion may be inaccurate. Consider using '#align continuous_on_Icc_extend_from_Ioo continuousOn_Icc_extendFrom_Iooₓ'. -/
theorem continuousOn_Icc_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la lb : β}
    (hab : a ≠ b) (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la))
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : ContinuousOn (extendFrom (Ioo a b) f) (Icc a b) :=
  by
  apply continuousOn_extendFrom
  · rw [closure_Ioo hab]
  · intro x x_in
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc x_in with (rfl | rfl | h)
    · exact ⟨la, ha.mono_left <| nhdsWithin_mono _ Ioo_subset_Ioi_self⟩
    · exact ⟨lb, hb.mono_left <| nhdsWithin_mono _ Ioo_subset_Iio_self⟩
    · use f x, hf x h
#align continuous_on_Icc_extend_from_Ioo continuousOn_Icc_extendFrom_Ioo

/- warning: eq_lim_at_left_extend_from_Ioo -> eq_lim_at_left_extendFrom_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))))] [_inst_4 : OrderTopology.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))] [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : T2Space.{u2} β _inst_5] {f : α -> β} {a : α} {b : α} {la : β}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a b) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a)) (nhds.{u2} β _inst_5 la)) -> (Eq.{succ u2} β (extendFrom.{u1, u2} α β _inst_1 _inst_5 (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a b) f a) la)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : DenselyOrdered.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))))] [_inst_4 : OrderTopology.{u2} α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2)))))] [_inst_5 : TopologicalSpace.{u1} β] [_inst_6 : T2Space.{u1} β _inst_5] {f : α -> β} {a : α} {b : α} {la : β}, (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2)))))) a b) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a (Set.Ioi.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a)) (nhds.{u1} β _inst_5 la)) -> (Eq.{succ u1} β (extendFrom.{u2, u1} α β _inst_1 _inst_5 (Set.Ioo.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a b) f a) la)
Case conversion may be inaccurate. Consider using '#align eq_lim_at_left_extend_from_Ioo eq_lim_at_left_extendFrom_Iooₓ'. -/
theorem eq_lim_at_left_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {la : β} (hab : a < b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 la)) : extendFrom (Ioo a b) f a = la :=
  by
  apply extendFrom_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc]
  · simpa [hab]
#align eq_lim_at_left_extend_from_Ioo eq_lim_at_left_extendFrom_Ioo

/- warning: eq_lim_at_right_extend_from_Ioo -> eq_lim_at_right_extendFrom_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))))] [_inst_4 : OrderTopology.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))] [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : T2Space.{u2} β _inst_5] {f : α -> β} {a : α} {b : α} {lb : β}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a b) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 b (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) b)) (nhds.{u2} β _inst_5 lb)) -> (Eq.{succ u2} β (extendFrom.{u1, u2} α β _inst_1 _inst_5 (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a b) f b) lb)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : DenselyOrdered.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))))] [_inst_4 : OrderTopology.{u2} α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2)))))] [_inst_5 : TopologicalSpace.{u1} β] [_inst_6 : T2Space.{u1} β _inst_5] {f : α -> β} {a : α} {b : α} {lb : β}, (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2)))))) a b) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 b (Set.Iio.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) b)) (nhds.{u1} β _inst_5 lb)) -> (Eq.{succ u1} β (extendFrom.{u2, u1} α β _inst_1 _inst_5 (Set.Ioo.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a b) f b) lb)
Case conversion may be inaccurate. Consider using '#align eq_lim_at_right_extend_from_Ioo eq_lim_at_right_extendFrom_Iooₓ'. -/
theorem eq_lim_at_right_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {lb : β} (hab : a < b)
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : extendFrom (Ioo a b) f b = lb :=
  by
  apply extendFrom_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc]
  · simpa [hab]
#align eq_lim_at_right_extend_from_Ioo eq_lim_at_right_extendFrom_Ioo

/- warning: continuous_on_Ico_extend_from_Ioo -> continuousOn_Ico_extendFrom_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))))] [_inst_4 : OrderTopology.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))] [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : RegularSpace.{u2} β _inst_5] {f : α -> β} {a : α} {b : α} {la : β}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a b) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_5 f (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a b)) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a)) (nhds.{u2} β _inst_5 la)) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_5 (extendFrom.{u1, u2} α β _inst_1 _inst_5 (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a b) f) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : DenselyOrdered.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))))] [_inst_4 : OrderTopology.{u2} α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2)))))] [_inst_5 : TopologicalSpace.{u1} β] [_inst_6 : RegularSpace.{u1} β _inst_5] {f : α -> β} {a : α} {b : α} {la : β}, (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2)))))) a b) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_5 f (Set.Ioo.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a b)) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 a (Set.Ioi.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a)) (nhds.{u1} β _inst_5 la)) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_5 (extendFrom.{u2, u1} α β _inst_1 _inst_5 (Set.Ioo.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a b) f) (Set.Ico.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a b))
Case conversion may be inaccurate. Consider using '#align continuous_on_Ico_extend_from_Ioo continuousOn_Ico_extendFrom_Iooₓ'. -/
theorem continuousOn_Ico_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la : β}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ico a b) :=
  by
  apply continuousOn_extendFrom
  · rw [closure_Ioo hab.ne]
    exact Ico_subset_Icc_self
  · intro x x_in
    rcases eq_left_or_mem_Ioo_of_mem_Ico x_in with (rfl | h)
    · use la
      simpa [hab]
    · use f x, hf x h
#align continuous_on_Ico_extend_from_Ioo continuousOn_Ico_extendFrom_Ioo

/- warning: continuous_on_Ioc_extend_from_Ioo -> continuousOn_Ioc_extendFrom_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))))] [_inst_4 : OrderTopology.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))] [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : RegularSpace.{u2} β _inst_5] {f : α -> β} {a : α} {b : α} {lb : β}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a b) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_5 f (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a b)) -> (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 b (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) b)) (nhds.{u2} β _inst_5 lb)) -> (ContinuousOn.{u1, u2} α β _inst_1 _inst_5 (extendFrom.{u1, u2} α β _inst_1 _inst_5 (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a b) f) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : DenselyOrdered.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))))] [_inst_4 : OrderTopology.{u2} α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2)))))] [_inst_5 : TopologicalSpace.{u1} β] [_inst_6 : RegularSpace.{u1} β _inst_5] {f : α -> β} {a : α} {b : α} {lb : β}, (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2)))))) a b) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_5 f (Set.Ioo.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a b)) -> (Filter.Tendsto.{u2, u1} α β f (nhdsWithin.{u2} α _inst_1 b (Set.Iio.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) b)) (nhds.{u1} β _inst_5 lb)) -> (ContinuousOn.{u2, u1} α β _inst_1 _inst_5 (extendFrom.{u2, u1} α β _inst_1 _inst_5 (Set.Ioo.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a b) f) (Set.Ioc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_2))))) a b))
Case conversion may be inaccurate. Consider using '#align continuous_on_Ioc_extend_from_Ioo continuousOn_Ioc_extendFrom_Iooₓ'. -/
theorem continuousOn_Ioc_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {lb : β}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b)) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ioc a b) :=
  by
  have := @continuousOn_Ico_extendFrom_Ioo αᵒᵈ _ _ _ _ _ _ _ f _ _ _ hab
  erw [dual_Ico, dual_Ioi, dual_Ioo] at this
  exact this hf hb
#align continuous_on_Ioc_extend_from_Ioo continuousOn_Ioc_extendFrom_Ioo

