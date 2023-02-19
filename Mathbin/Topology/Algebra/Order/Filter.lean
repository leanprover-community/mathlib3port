/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.filter
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order.Basic
import Mathbin.Topology.Filter

/-!
# Topology on filters of a space with order topology

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that `𝓝 (f x)` tends to `𝓝 filter.at_top` provided that `f` tends to
`filter.at_top`, and similarly for `filter.at_bot`.
-/


open Topology

namespace Filter

variable {α X : Type _} [TopologicalSpace X] [PartialOrder X] [OrderTopology X]

/- warning: filter.tendsto_nhds_at_top -> Filter.tendsto_nhds_atTop is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : PartialOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X _inst_2)] [_inst_4 : NoMaxOrder.{u1} X (Preorder.toLT.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2))], Filter.Tendsto.{u1, u1} X (Filter.{u1} X) (nhds.{u1} X _inst_1) (Filter.atTop.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2)) (nhds.{u1} (Filter.{u1} X) (Filter.topologicalSpace.{u1} X) (Filter.atTop.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : PartialOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X _inst_2)] [_inst_4 : NoMaxOrder.{u1} X (Preorder.toLT.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2))], Filter.Tendsto.{u1, u1} X (Filter.{u1} X) (nhds.{u1} X _inst_1) (Filter.atTop.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2)) (nhds.{u1} (Filter.{u1} X) (Filter.instTopologicalSpaceFilter.{u1} X) (Filter.atTop.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_nhds_at_top Filter.tendsto_nhds_atTopₓ'. -/
protected theorem tendsto_nhds_atTop [NoMaxOrder X] : Tendsto 𝓝 (atTop : Filter X) (𝓝 atTop) :=
  Filter.tendsto_nhds_atTop_iff.2 fun x => (eventually_gt_atTop x).mono fun y => le_mem_nhds
#align filter.tendsto_nhds_at_top Filter.tendsto_nhds_atTop

/- warning: filter.tendsto_nhds_at_bot -> Filter.tendsto_nhds_atBot is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : PartialOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X _inst_2)] [_inst_4 : NoMinOrder.{u1} X (Preorder.toLT.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2))], Filter.Tendsto.{u1, u1} X (Filter.{u1} X) (nhds.{u1} X _inst_1) (Filter.atBot.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2)) (nhds.{u1} (Filter.{u1} X) (Filter.topologicalSpace.{u1} X) (Filter.atBot.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : PartialOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X _inst_2)] [_inst_4 : NoMinOrder.{u1} X (Preorder.toLT.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2))], Filter.Tendsto.{u1, u1} X (Filter.{u1} X) (nhds.{u1} X _inst_1) (Filter.atBot.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2)) (nhds.{u1} (Filter.{u1} X) (Filter.instTopologicalSpaceFilter.{u1} X) (Filter.atBot.{u1} X (PartialOrder.toPreorder.{u1} X _inst_2)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_nhds_at_bot Filter.tendsto_nhds_atBotₓ'. -/
protected theorem tendsto_nhds_atBot [NoMinOrder X] : Tendsto 𝓝 (atBot : Filter X) (𝓝 atBot) :=
  @Filter.tendsto_nhds_atTop Xᵒᵈ _ _ _ _
#align filter.tendsto_nhds_at_bot Filter.tendsto_nhds_atBot

/- warning: filter.tendsto.nhds_at_top -> Filter.Tendsto.nhds_atTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : PartialOrder.{u2} X] [_inst_3 : OrderTopology.{u2} X _inst_1 (PartialOrder.toPreorder.{u2} X _inst_2)] [_inst_4 : NoMaxOrder.{u2} X (Preorder.toLT.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))] {f : α -> X} {l : Filter.{u1} α}, (Filter.Tendsto.{u1, u2} α X f l (Filter.atTop.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))) -> (Filter.Tendsto.{u1, u2} α (Filter.{u2} X) (Function.comp.{succ u1, succ u2, succ u2} α X (Filter.{u2} X) (nhds.{u2} X _inst_1) f) l (nhds.{u2} (Filter.{u2} X) (Filter.topologicalSpace.{u2} X) (Filter.atTop.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : PartialOrder.{u2} X] [_inst_3 : OrderTopology.{u2} X _inst_1 (PartialOrder.toPreorder.{u2} X _inst_2)] [_inst_4 : NoMaxOrder.{u2} X (Preorder.toLT.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))] {f : α -> X} {l : Filter.{u1} α}, (Filter.Tendsto.{u1, u2} α X f l (Filter.atTop.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))) -> (Filter.Tendsto.{u1, u2} α (Filter.{u2} X) (Function.comp.{succ u1, succ u2, succ u2} α X (Filter.{u2} X) (nhds.{u2} X _inst_1) f) l (nhds.{u2} (Filter.{u2} X) (Filter.instTopologicalSpaceFilter.{u2} X) (Filter.atTop.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.nhds_at_top Filter.Tendsto.nhds_atTopₓ'. -/
theorem Tendsto.nhds_atTop [NoMaxOrder X] {f : α → X} {l : Filter α} (h : Tendsto f l atTop) :
    Tendsto (𝓝 ∘ f) l (𝓝 atTop) :=
  Filter.tendsto_nhds_atTop.comp h
#align filter.tendsto.nhds_at_top Filter.Tendsto.nhds_atTop

/- warning: filter.tendsto.nhds_at_bot -> Filter.Tendsto.nhds_atBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : PartialOrder.{u2} X] [_inst_3 : OrderTopology.{u2} X _inst_1 (PartialOrder.toPreorder.{u2} X _inst_2)] [_inst_4 : NoMinOrder.{u2} X (Preorder.toLT.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))] {f : α -> X} {l : Filter.{u1} α}, (Filter.Tendsto.{u1, u2} α X f l (Filter.atBot.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))) -> (Filter.Tendsto.{u1, u2} α (Filter.{u2} X) (Function.comp.{succ u1, succ u2, succ u2} α X (Filter.{u2} X) (nhds.{u2} X _inst_1) f) l (nhds.{u2} (Filter.{u2} X) (Filter.topologicalSpace.{u2} X) (Filter.atBot.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : PartialOrder.{u2} X] [_inst_3 : OrderTopology.{u2} X _inst_1 (PartialOrder.toPreorder.{u2} X _inst_2)] [_inst_4 : NoMinOrder.{u2} X (Preorder.toLT.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))] {f : α -> X} {l : Filter.{u1} α}, (Filter.Tendsto.{u1, u2} α X f l (Filter.atBot.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))) -> (Filter.Tendsto.{u1, u2} α (Filter.{u2} X) (Function.comp.{succ u1, succ u2, succ u2} α X (Filter.{u2} X) (nhds.{u2} X _inst_1) f) l (nhds.{u2} (Filter.{u2} X) (Filter.instTopologicalSpaceFilter.{u2} X) (Filter.atBot.{u2} X (PartialOrder.toPreorder.{u2} X _inst_2))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.nhds_at_bot Filter.Tendsto.nhds_atBotₓ'. -/
theorem Tendsto.nhds_atBot [NoMinOrder X] {f : α → X} {l : Filter α} (h : Tendsto f l atBot) :
    Tendsto (𝓝 ∘ f) l (𝓝 atBot) :=
  @Tendsto.nhds_atTop α Xᵒᵈ _ _ _ _ _ _ h
#align filter.tendsto.nhds_at_bot Filter.Tendsto.nhds_atBot

end Filter

