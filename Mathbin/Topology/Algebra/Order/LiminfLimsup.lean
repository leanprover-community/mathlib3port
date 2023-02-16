/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.liminf_limsup
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Intervals
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Algebra.IndicatorFunction
import Mathbin.Order.LiminfLimsup
import Mathbin.Order.Filter.Archimedean
import Mathbin.Topology.Order.Basic

/-!
# Lemmas about liminf and limsup in an order topology.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Filter

open Topology Classical

universe u v

variable {α : Type u} {β : Type v}

section LiminfLimsup

section OrderClosedTopology

variable [SemilatticeSup α] [TopologicalSpace α] [OrderTopology α]

#print isBounded_le_nhds /-
theorem isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·) :=
  (isTop_or_exists_gt a).elim (fun h => ⟨a, eventually_of_forall h⟩) fun ⟨b, hb⟩ =>
    ⟨b, ge_mem_nhds hb⟩
#align is_bounded_le_nhds isBounded_le_nhds
-/

#print Filter.Tendsto.isBoundedUnder_le /-
theorem Filter.Tendsto.isBoundedUnder_le {f : Filter β} {u : β → α} {a : α}
    (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≤ ·) u :=
  (isBounded_le_nhds a).mono h
#align filter.tendsto.is_bounded_under_le Filter.Tendsto.isBoundedUnder_le
-/

#print Filter.Tendsto.bddAbove_range_of_cofinite /-
theorem Filter.Tendsto.bddAbove_range_of_cofinite {u : β → α} {a : α}
    (h : Tendsto u cofinite (𝓝 a)) : BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range_of_cofinite
#align filter.tendsto.bdd_above_range_of_cofinite Filter.Tendsto.bddAbove_range_of_cofinite
-/

#print Filter.Tendsto.bddAbove_range /-
theorem Filter.Tendsto.bddAbove_range {u : ℕ → α} {a : α} (h : Tendsto u atTop (𝓝 a)) :
    BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range
#align filter.tendsto.bdd_above_range Filter.Tendsto.bddAbove_range
-/

#print isCobounded_ge_nhds /-
theorem isCobounded_ge_nhds (a : α) : (𝓝 a).IsCobounded (· ≥ ·) :=
  (isBounded_le_nhds a).isCobounded_flip
#align is_cobounded_ge_nhds isCobounded_ge_nhds
-/

#print Filter.Tendsto.isCoboundedUnder_ge /-
theorem Filter.Tendsto.isCoboundedUnder_ge {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : f.IsCoboundedUnder (· ≥ ·) u :=
  h.isBoundedUnder_le.isCobounded_flip
#align filter.tendsto.is_cobounded_under_ge Filter.Tendsto.isCoboundedUnder_ge
-/

#print isBounded_le_atBot /-
theorem isBounded_le_atBot (α : Type _) [hα : Nonempty α] [Preorder α] :
    (atBot : Filter α).IsBounded (· ≤ ·) :=
  isBounded_iff.2 ⟨Set.Iic hα.some, mem_atBot _, hα.some, fun x hx => hx⟩
#align is_bounded_le_at_bot isBounded_le_atBot
-/

/- warning: filter.tendsto.is_bounded_under_le_at_bot -> Filter.Tendsto.isBoundedUnder_le_atBot is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_4 : Nonempty.{succ u2} α] [_inst_5 : Preorder.{u2} α] {f : Filter.{u1} β} {u : β -> α}, (Filter.Tendsto.{u1, u2} β α u f (Filter.atBot.{u2} α _inst_5)) -> (Filter.IsBoundedUnder.{u2, u1} α β (LE.le.{u2} α (Preorder.toLE.{u2} α _inst_5)) f u)
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u1}} [_inst_4 : Nonempty.{succ u1} α] [_inst_5 : Preorder.{u1} α] {f : Filter.{u2} β} {u : β -> α}, (Filter.Tendsto.{u2, u1} β α u f (Filter.atBot.{u1} α _inst_5)) -> (Filter.IsBoundedUnder.{u1, u2} α β (fun (x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.426 : α) (x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.428 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_5) x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.426 x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.428) f u)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.is_bounded_under_le_at_bot Filter.Tendsto.isBoundedUnder_le_atBotₓ'. -/
theorem Filter.Tendsto.isBoundedUnder_le_atBot {α : Type _} [Nonempty α] [Preorder α] {f : Filter β}
    {u : β → α} (h : Tendsto u f atBot) : f.IsBoundedUnder (· ≤ ·) u :=
  (isBounded_le_atBot α).mono h
#align filter.tendsto.is_bounded_under_le_at_bot Filter.Tendsto.isBoundedUnder_le_atBot

#print bddAbove_range_of_tendsto_atTop_atBot /-
theorem bddAbove_range_of_tendsto_atTop_atBot {α : Type _} [Nonempty α] [SemilatticeSup α]
    {u : ℕ → α} (hx : Tendsto u atTop atBot) : BddAbove (Set.range u) :=
  (Filter.Tendsto.isBoundedUnder_le_atBot hx).bddAbove_range
#align bdd_above_range_of_tendsto_at_top_at_bot bddAbove_range_of_tendsto_atTop_atBot
-/

end OrderClosedTopology

section OrderClosedTopology

variable [SemilatticeInf α] [TopologicalSpace α] [OrderTopology α]

#print isBounded_ge_nhds /-
theorem isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·) :=
  @isBounded_le_nhds αᵒᵈ _ _ _ a
#align is_bounded_ge_nhds isBounded_ge_nhds
-/

#print Filter.Tendsto.isBoundedUnder_ge /-
theorem Filter.Tendsto.isBoundedUnder_ge {f : Filter β} {u : β → α} {a : α}
    (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≥ ·) u :=
  (isBounded_ge_nhds a).mono h
#align filter.tendsto.is_bounded_under_ge Filter.Tendsto.isBoundedUnder_ge
-/

#print Filter.Tendsto.bddBelow_range_of_cofinite /-
theorem Filter.Tendsto.bddBelow_range_of_cofinite {u : β → α} {a : α}
    (h : Tendsto u cofinite (𝓝 a)) : BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range_of_cofinite
#align filter.tendsto.bdd_below_range_of_cofinite Filter.Tendsto.bddBelow_range_of_cofinite
-/

#print Filter.Tendsto.bddBelow_range /-
theorem Filter.Tendsto.bddBelow_range {u : ℕ → α} {a : α} (h : Tendsto u atTop (𝓝 a)) :
    BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range
#align filter.tendsto.bdd_below_range Filter.Tendsto.bddBelow_range
-/

#print isCobounded_le_nhds /-
theorem isCobounded_le_nhds (a : α) : (𝓝 a).IsCobounded (· ≤ ·) :=
  (isBounded_ge_nhds a).isCobounded_flip
#align is_cobounded_le_nhds isCobounded_le_nhds
-/

#print Filter.Tendsto.isCoboundedUnder_le /-
theorem Filter.Tendsto.isCoboundedUnder_le {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : f.IsCoboundedUnder (· ≤ ·) u :=
  h.isBoundedUnder_ge.isCobounded_flip
#align filter.tendsto.is_cobounded_under_le Filter.Tendsto.isCoboundedUnder_le
-/

#print isBounded_ge_atTop /-
theorem isBounded_ge_atTop (α : Type _) [hα : Nonempty α] [Preorder α] :
    (atTop : Filter α).IsBounded (· ≥ ·) :=
  isBounded_le_atBot αᵒᵈ
#align is_bounded_ge_at_top isBounded_ge_atTop
-/

/- warning: filter.tendsto.is_bounded_under_ge_at_top -> Filter.Tendsto.isBoundedUnder_ge_atTop is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_4 : Nonempty.{succ u2} α] [_inst_5 : Preorder.{u2} α] {f : Filter.{u1} β} {u : β -> α}, (Filter.Tendsto.{u1, u2} β α u f (Filter.atTop.{u2} α _inst_5)) -> (Filter.IsBoundedUnder.{u2, u1} α β (GE.ge.{u2} α (Preorder.toLE.{u2} α _inst_5)) f u)
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u1}} [_inst_4 : Nonempty.{succ u1} α] [_inst_5 : Preorder.{u1} α] {f : Filter.{u2} β} {u : β -> α}, (Filter.Tendsto.{u2, u1} β α u f (Filter.atTop.{u1} α _inst_5)) -> (Filter.IsBoundedUnder.{u1, u2} α β (fun (x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.855 : α) (x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.857 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_5) x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.855 x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.857) f u)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.is_bounded_under_ge_at_top Filter.Tendsto.isBoundedUnder_ge_atTopₓ'. -/
theorem Filter.Tendsto.isBoundedUnder_ge_atTop {α : Type _} [Nonempty α] [Preorder α] {f : Filter β}
    {u : β → α} (h : Tendsto u f atTop) : f.IsBoundedUnder (· ≥ ·) u :=
  (isBounded_ge_atTop α).mono h
#align filter.tendsto.is_bounded_under_ge_at_top Filter.Tendsto.isBoundedUnder_ge_atTop

#print bddBelow_range_of_tendsto_atTop_atTop /-
theorem bddBelow_range_of_tendsto_atTop_atTop {α : Type _} [Nonempty α] [SemilatticeInf α]
    {u : ℕ → α} (hx : Tendsto u atTop atTop) : BddBelow (Set.range u) :=
  (Filter.Tendsto.isBoundedUnder_ge_atTop hx).bddBelow_range
#align bdd_below_range_of_tendsto_at_top_at_top bddBelow_range_of_tendsto_atTop_atTop
-/

end OrderClosedTopology

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α]

#print lt_mem_sets_of_limsupₛ_lt /-
theorem lt_mem_sets_of_limsupₛ_lt {f : Filter α} {b} (h : f.IsBounded (· ≤ ·)) (l : f.limsupₛ < b) :
    ∀ᶠ a in f, a < b :=
  let ⟨c, (h : ∀ᶠ a in f, a ≤ c), hcb⟩ := exists_lt_of_cinfₛ_lt h l
  mem_of_superset h fun a hac => lt_of_le_of_lt hac hcb
#align lt_mem_sets_of_Limsup_lt lt_mem_sets_of_limsupₛ_lt
-/

#print gt_mem_sets_of_liminfₛ_gt /-
theorem gt_mem_sets_of_liminfₛ_gt :
    ∀ {f : Filter α} {b}, f.IsBounded (· ≥ ·) → b < f.liminfₛ → ∀ᶠ a in f, b < a :=
  @lt_mem_sets_of_limsupₛ_lt αᵒᵈ _
#align gt_mem_sets_of_Liminf_gt gt_mem_sets_of_liminfₛ_gt
-/

variable [TopologicalSpace α] [OrderTopology α]

/- warning: le_nhds_of_Limsup_eq_Liminf -> le_nhds_of_limsupₛ_eq_liminfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))] {f : Filter.{u1} α} {a : α}, (Filter.IsBounded.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))))) f) -> (Filter.IsBounded.{u1} α (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))))) f) -> (Eq.{succ u1} α (Filter.limsupₛ.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1) f) a) -> (Eq.{succ u1} α (Filter.liminfₛ.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1) f) a) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α _inst_2 a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))] {f : Filter.{u1} α} {a : α}, (Filter.IsBounded.{u1} α (fun (x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.1145 : α) (x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.1147 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.1145 x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.1147) f) -> (Filter.IsBounded.{u1} α (fun (x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.1161 : α) (x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.1163 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.1161 x._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.1163) f) -> (Eq.{succ u1} α (Filter.limsupₛ.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1) f) a) -> (Eq.{succ u1} α (Filter.liminfₛ.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1) f) a) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α _inst_2 a))
Case conversion may be inaccurate. Consider using '#align le_nhds_of_Limsup_eq_Liminf le_nhds_of_limsupₛ_eq_liminfₛₓ'. -/
/-- If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below. -/
theorem le_nhds_of_limsupₛ_eq_liminfₛ {f : Filter α} {a : α} (hl : f.IsBounded (· ≤ ·))
    (hg : f.IsBounded (· ≥ ·)) (hs : f.limsupₛ = a) (hi : f.liminfₛ = a) : f ≤ 𝓝 a :=
  tendsto_order.2 <|
    And.intro (fun b hb => gt_mem_sets_of_liminfₛ_gt hg <| hi.symm ▸ hb) fun b hb =>
      lt_mem_sets_of_limsupₛ_lt hl <| hs.symm ▸ hb
#align le_nhds_of_Limsup_eq_Liminf le_nhds_of_limsupₛ_eq_liminfₛ

#print limsupₛ_nhds /-
theorem limsupₛ_nhds (a : α) : limsupₛ (𝓝 a) = a :=
  cinfₛ_eq_of_forall_ge_of_forall_gt_exists_lt (isBounded_le_nhds a)
    (fun a' (h : { n : α | n ≤ a' } ∈ 𝓝 a) => show a ≤ a' from @mem_of_mem_nhds α _ a _ h)
    fun b (hba : a < b) =>
    show ∃ (c : _)(h : { n : α | n ≤ c } ∈ 𝓝 a), c < b from
      match dense_or_discrete a b with
      | Or.inl ⟨c, hac, hcb⟩ => ⟨c, ge_mem_nhds hac, hcb⟩
      | Or.inr ⟨_, h⟩ => ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩
#align Limsup_nhds limsupₛ_nhds
-/

#print liminfₛ_nhds /-
theorem liminfₛ_nhds : ∀ a : α, liminfₛ (𝓝 a) = a :=
  @limsupₛ_nhds αᵒᵈ _ _ _
#align Liminf_nhds liminfₛ_nhds
-/

/- warning: Liminf_eq_of_le_nhds -> liminfₛ_eq_of_le_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))] {f : Filter.{u1} α} {a : α} [_inst_4 : Filter.NeBot.{u1} α f], (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α _inst_2 a)) -> (Eq.{succ u1} α (Filter.liminfₛ.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1) f) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))] {f : Filter.{u1} α} {a : α} [_inst_4 : Filter.NeBot.{u1} α f], (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α _inst_2 a)) -> (Eq.{succ u1} α (Filter.liminfₛ.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1) f) a)
Case conversion may be inaccurate. Consider using '#align Liminf_eq_of_le_nhds liminfₛ_eq_of_le_nhdsₓ'. -/
/-- If a filter is converging, its limsup coincides with its limit. -/
theorem liminfₛ_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f ≤ 𝓝 a) : f.liminfₛ = a :=
  have hb_ge : IsBounded (· ≥ ·) f := (isBounded_ge_nhds a).mono h
  have hb_le : IsBounded (· ≤ ·) f := (isBounded_le_nhds a).mono h
  le_antisymm
    (calc
      f.liminfₛ ≤ f.limsupₛ := liminfₛ_le_limsupₛ hb_le hb_ge
      _ ≤ (𝓝 a).limsupₛ := limsupₛ_le_limsupₛ_of_le h hb_ge.isCobounded_flip (isBounded_le_nhds a)
      _ = a := limsupₛ_nhds a
      )
    (calc
      a = (𝓝 a).liminfₛ := (liminfₛ_nhds a).symm
      _ ≤ f.liminfₛ := liminfₛ_le_liminfₛ_of_le h (isBounded_ge_nhds a) hb_le.isCobounded_flip
      )
#align Liminf_eq_of_le_nhds liminfₛ_eq_of_le_nhds

/- warning: Limsup_eq_of_le_nhds -> limsupₛ_eq_of_le_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))] {f : Filter.{u1} α} {a : α} [_inst_4 : Filter.NeBot.{u1} α f], (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α _inst_2 a)) -> (Eq.{succ u1} α (Filter.limsupₛ.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1) f) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))] {f : Filter.{u1} α} {a : α} [_inst_4 : Filter.NeBot.{u1} α f], (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α _inst_2 a)) -> (Eq.{succ u1} α (Filter.limsupₛ.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1) f) a)
Case conversion may be inaccurate. Consider using '#align Limsup_eq_of_le_nhds limsupₛ_eq_of_le_nhdsₓ'. -/
/-- If a filter is converging, its liminf coincides with its limit. -/
theorem limsupₛ_eq_of_le_nhds : ∀ {f : Filter α} {a : α} [NeBot f], f ≤ 𝓝 a → f.limsupₛ = a :=
  @liminfₛ_eq_of_le_nhds αᵒᵈ _ _ _
#align Limsup_eq_of_le_nhds limsupₛ_eq_of_le_nhds

#print Filter.Tendsto.limsup_eq /-
/-- If a function has a limit, then its limsup coincides with its limit. -/
theorem Filter.Tendsto.limsup_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : limsup u f = a :=
  limsupₛ_eq_of_le_nhds h
#align filter.tendsto.limsup_eq Filter.Tendsto.limsup_eq
-/

#print Filter.Tendsto.liminf_eq /-
/-- If a function has a limit, then its liminf coincides with its limit. -/
theorem Filter.Tendsto.liminf_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : liminf u f = a :=
  liminfₛ_eq_of_le_nhds h
#align filter.tendsto.liminf_eq Filter.Tendsto.liminf_eq
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic is_bounded_default -/
#print tendsto_of_liminf_eq_limsup /-
/-- If the liminf and the limsup of a function coincide, then the limit of the function
exists and has the same value -/
theorem tendsto_of_liminf_eq_limsup {f : Filter β} {u : β → α} {a : α} (hinf : liminf u f = a)
    (hsup : limsup u f = a)
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    Tendsto u f (𝓝 a) :=
  le_nhds_of_limsupₛ_eq_liminfₛ h h' hsup hinf
#align tendsto_of_liminf_eq_limsup tendsto_of_liminf_eq_limsup
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic is_bounded_default -/
#print tendsto_of_le_liminf_of_limsup_le /-
/-- If a number `a` is less than or equal to the `liminf` of a function `f` at some filter
and is greater than or equal to the `limsup` of `f`, then `f` tends to `a` along this filter. -/
theorem tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β → α} {a : α} (hinf : a ≤ liminf u f)
    (hsup : limsup u f ≤ a)
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    Tendsto u f (𝓝 a) :=
  if hf : f = ⊥ then hf.symm ▸ tendsto_bot
  else
    haveI : ne_bot f := ⟨hf⟩
    tendsto_of_liminf_eq_limsup (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf)
      (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h'
#align tendsto_of_le_liminf_of_limsup_le tendsto_of_le_liminf_of_limsup_le
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic is_bounded_default -/
#print tendsto_of_no_upcrossings /-
/-- Assume that, for any `a < b`, a sequence can not be infinitely many times below `a` and
above `b`. If it is also ultimately bounded above and below, then it has to converge. This even
works if `a` and `b` are restricted to a dense subset.
-/
theorem tendsto_of_no_upcrossings [DenselyOrdered α] {f : Filter β} {u : β → α} {s : Set α}
    (hs : Dense s) (H : ∀ a ∈ s, ∀ b ∈ s, a < b → ¬((∃ᶠ n in f, u n < a) ∧ ∃ᶠ n in f, b < u n))
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    ∃ c : α, Tendsto u f (𝓝 c) := by
  by_cases hbot : f = ⊥;
  · rw [hbot]
    exact ⟨Inf ∅, tendsto_bot⟩
  haveI : ne_bot f := ⟨hbot⟩
  refine' ⟨limsup u f, _⟩
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h'
  by_contra' hlt
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : ∃ a, (f.liminf u < a ∧ a < f.limsup u) ∧ a ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo (f.liminf u) (f.limsup u)) isOpen_Ioo
      (Set.nonempty_Ioo.2 hlt)
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : ∃ b, (a < b ∧ b < f.limsup u) ∧ b ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo a (f.limsup u)) isOpen_Ioo (Set.nonempty_Ioo.2 au)
  have A : ∃ᶠ n in f, u n < a := frequently_lt_of_liminf_lt (is_bounded.is_cobounded_ge h) la
  have B : ∃ᶠ n in f, b < u n := frequently_lt_of_lt_limsup (is_bounded.is_cobounded_le h') bu
  exact H a as b bs ab ⟨A, B⟩
#align tendsto_of_no_upcrossings tendsto_of_no_upcrossings
-/

end ConditionallyCompleteLinearOrder

end LiminfLimsup

section Monotone

variable {ι R S : Type _} {F : Filter ι} [NeBot F] [CompleteLinearOrder R] [TopologicalSpace R]
  [OrderTopology R] [CompleteLinearOrder S] [TopologicalSpace S] [OrderTopology S]

/- warning: antitone.map_Limsup_of_continuous_at -> Antitone.map_limsupₛ_of_continuousAt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : CompleteLinearOrder.{u1} R] [_inst_3 : TopologicalSpace.{u1} R] [_inst_4 : OrderTopology.{u1} R _inst_3 (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u2} S] [_inst_6 : TopologicalSpace.{u2} S] [_inst_7 : OrderTopology.{u2} S _inst_6 (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5))))] {F : Filter.{u1} R} [_inst_8 : Filter.NeBot.{u1} R F] {f : R -> S}, (Antitone.{u1, u2} R S (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)))) f) -> (ContinuousAt.{u1, u2} R S _inst_3 _inst_6 f (Filter.limsupₛ.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) F)) -> (Eq.{succ u2} S (f (Filter.limsupₛ.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) F)) (Filter.liminf.{u2, u1} S R (CompleteLattice.toConditionallyCompleteLattice.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)) f F))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_2 : CompleteLinearOrder.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : OrderTopology.{u2} R _inst_3 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u1} S] [_inst_6 : TopologicalSpace.{u1} S] [_inst_7 : OrderTopology.{u1} S _inst_6 (PartialOrder.toPreorder.{u1} S (CompleteSemilatticeInf.toPartialOrder.{u1} S (CompleteLattice.toCompleteSemilatticeInf.{u1} S (CompleteLinearOrder.toCompleteLattice.{u1} S _inst_5))))] {F : Filter.{u2} R} [_inst_8 : Filter.NeBot.{u2} R F] {f : R -> S}, (Antitone.{u2, u1} R S (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (PartialOrder.toPreorder.{u1} S (CompleteSemilatticeInf.toPartialOrder.{u1} S (CompleteLattice.toCompleteSemilatticeInf.{u1} S (CompleteLinearOrder.toCompleteLattice.{u1} S _inst_5)))) f) -> (ContinuousAt.{u2, u1} R S _inst_3 _inst_6 f (Filter.limsupₛ.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} R _inst_2))) F)) -> (Eq.{succ u1} S (f (Filter.limsupₛ.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} R _inst_2))) F)) (Filter.liminf.{u1, u2} S R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} S (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} S (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u1} S _inst_5))) f F))
Case conversion may be inaccurate. Consider using '#align antitone.map_Limsup_of_continuous_at Antitone.map_limsupₛ_of_continuousAtₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic filter.is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic filter.is_bounded_default -/
/-- An antitone function between complete linear ordered spaces sends a `filter.Limsup`
to the `filter.liminf` of the image if it is continuous at the `Limsup`. -/
theorem Antitone.map_limsupₛ_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsupₛ) : f F.limsupₛ = F.liminf f :=
  by
  apply le_antisymm
  · have A : { a : R | ∀ᶠ n : R in F, n ≤ a }.Nonempty := ⟨⊤, by simp⟩
    rw [Limsup, f_decr.map_Inf_of_continuous_at' f_cont A]
    apply le_of_forall_lt
    intro c hc
    simp only [liminf, Liminf, lt_supₛ_iff, eventually_map, Set.mem_setOf_eq, exists_prop,
      Set.mem_image, exists_exists_and_eq_and] at hc⊢
    rcases hc with ⟨d, hd, h'd⟩
    refine' ⟨f d, _, h'd⟩
    filter_upwards [hd]with x hx using f_decr hx
  · rcases eq_or_lt_of_le (bot_le : ⊥ ≤ F.Limsup) with (h | Limsup_ne_bot)
    · rw [← h]
      apply liminf_le_of_frequently_le
      apply frequently_of_forall
      intro x
      exact f_decr bot_le
    by_cases h' : ∃ c, c < F.Limsup ∧ Set.Ioo c F.Limsup = ∅
    · rcases h' with ⟨c, c_lt, hc⟩
      have B : ∃ᶠ n in F, F.Limsup ≤ n :=
        by
        apply
          (frequently_lt_of_lt_Limsup
              (by
                run_tac
                  is_bounded_default)
              c_lt).mono
        intro x hx
        by_contra'
        have : (Set.Ioo c F.Limsup).Nonempty := ⟨x, ⟨hx, this⟩⟩
        simpa [hc]
      apply liminf_le_of_frequently_le
      exact B.mono fun x hx => f_decr hx
    by_contra' H
    obtain ⟨l, l_lt, h'l⟩ : ∃ l < F.Limsup, Set.Ioc l F.Limsup ⊆ { x : R | f x < F.liminf f }
    exact exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H) ⟨⊥, Limsup_ne_bot⟩
    obtain ⟨m, l_m, m_lt⟩ : (Set.Ioo l F.Limsup).Nonempty :=
      by
      contrapose! h'
      refine' ⟨l, l_lt, by rwa [Set.not_nonempty_iff_eq_empty] at h'⟩
    have B : F.liminf f ≤ f m := by
      apply liminf_le_of_frequently_le
      apply
        (frequently_lt_of_lt_Limsup
            (by
              run_tac
                is_bounded_default)
            m_lt).mono
      intro x hx
      exact f_decr hx.le
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩
    exact lt_irrefl _ (B.trans_lt I)
#align antitone.map_Limsup_of_continuous_at Antitone.map_limsupₛ_of_continuousAt

/- warning: antitone.map_limsup_of_continuous_at -> Antitone.map_limsup_of_continuousAt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} {F : Filter.{u1} ι} [_inst_1 : Filter.NeBot.{u1} ι F] [_inst_2 : CompleteLinearOrder.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : OrderTopology.{u2} R _inst_3 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u3} S] [_inst_6 : TopologicalSpace.{u3} S] [_inst_7 : OrderTopology.{u3} S _inst_6 (PartialOrder.toPreorder.{u3} S (CompleteSemilatticeInf.toPartialOrder.{u3} S (CompleteLattice.toCompleteSemilatticeInf.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5))))] {f : R -> S}, (Antitone.{u2, u3} R S (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (PartialOrder.toPreorder.{u3} S (CompleteSemilatticeInf.toPartialOrder.{u3} S (CompleteLattice.toCompleteSemilatticeInf.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5)))) f) -> (forall (a : ι -> R), (ContinuousAt.{u2, u3} R S _inst_3 _inst_6 f (Filter.limsup.{u2, u1} R ι (CompleteLattice.toConditionallyCompleteLattice.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)) a F)) -> (Eq.{succ u3} S (f (Filter.limsup.{u2, u1} R ι (CompleteLattice.toConditionallyCompleteLattice.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)) a F)) (Filter.liminf.{u3, u1} S ι (CompleteLattice.toConditionallyCompleteLattice.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5)) (Function.comp.{succ u1, succ u2, succ u3} ι R S f a) F)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} {F : Filter.{u1} ι} [_inst_1 : Filter.NeBot.{u1} ι F] [_inst_2 : CompleteLinearOrder.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_4 : OrderTopology.{u3} R _inst_3 (PartialOrder.toPreorder.{u3} R (CompleteSemilatticeInf.toPartialOrder.{u3} R (CompleteLattice.toCompleteSemilatticeInf.{u3} R (CompleteLinearOrder.toCompleteLattice.{u3} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u2} S] [_inst_6 : TopologicalSpace.{u2} S] [_inst_7 : OrderTopology.{u2} S _inst_6 (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5))))] {f : R -> S}, (Antitone.{u3, u2} R S (PartialOrder.toPreorder.{u3} R (CompleteSemilatticeInf.toPartialOrder.{u3} R (CompleteLattice.toCompleteSemilatticeInf.{u3} R (CompleteLinearOrder.toCompleteLattice.{u3} R _inst_2)))) (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)))) f) -> (forall (a : ι -> R), (ContinuousAt.{u3, u2} R S _inst_3 _inst_6 f (Filter.limsup.{u3, u1} R ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u3} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u3} R _inst_2))) a F)) -> (Eq.{succ u2} S (f (Filter.limsup.{u3, u1} R ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u3} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u3} R _inst_2))) a F)) (Filter.liminf.{u2, u1} S ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} S (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} S (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} S _inst_5))) (Function.comp.{succ u1, succ u3, succ u2} ι R S f a) F)))
Case conversion may be inaccurate. Consider using '#align antitone.map_limsup_of_continuous_at Antitone.map_limsup_of_continuousAtₓ'. -/
/-- A continuous antitone function between complete linear ordered spaces sends a `filter.limsup`
to the `filter.liminf` of the images. -/
theorem Antitone.map_limsup_of_continuousAt {f : R → S} (f_decr : Antitone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.limsup a)) : f (F.limsup a) = F.liminf (f ∘ a) :=
  f_decr.map_limsupₛ_of_continuousAt f_cont
#align antitone.map_limsup_of_continuous_at Antitone.map_limsup_of_continuousAt

/- warning: antitone.map_Liminf_of_continuous_at -> Antitone.map_liminfₛ_of_continuousAt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : CompleteLinearOrder.{u1} R] [_inst_3 : TopologicalSpace.{u1} R] [_inst_4 : OrderTopology.{u1} R _inst_3 (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u2} S] [_inst_6 : TopologicalSpace.{u2} S] [_inst_7 : OrderTopology.{u2} S _inst_6 (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5))))] {F : Filter.{u1} R} [_inst_8 : Filter.NeBot.{u1} R F] {f : R -> S}, (Antitone.{u1, u2} R S (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)))) f) -> (ContinuousAt.{u1, u2} R S _inst_3 _inst_6 f (Filter.liminfₛ.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) F)) -> (Eq.{succ u2} S (f (Filter.liminfₛ.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) F)) (Filter.limsup.{u2, u1} S R (CompleteLattice.toConditionallyCompleteLattice.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)) f F))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_2 : CompleteLinearOrder.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : OrderTopology.{u2} R _inst_3 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u1} S] [_inst_6 : TopologicalSpace.{u1} S] [_inst_7 : OrderTopology.{u1} S _inst_6 (PartialOrder.toPreorder.{u1} S (CompleteSemilatticeInf.toPartialOrder.{u1} S (CompleteLattice.toCompleteSemilatticeInf.{u1} S (CompleteLinearOrder.toCompleteLattice.{u1} S _inst_5))))] {F : Filter.{u2} R} [_inst_8 : Filter.NeBot.{u2} R F] {f : R -> S}, (Antitone.{u2, u1} R S (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (PartialOrder.toPreorder.{u1} S (CompleteSemilatticeInf.toPartialOrder.{u1} S (CompleteLattice.toCompleteSemilatticeInf.{u1} S (CompleteLinearOrder.toCompleteLattice.{u1} S _inst_5)))) f) -> (ContinuousAt.{u2, u1} R S _inst_3 _inst_6 f (Filter.liminfₛ.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} R _inst_2))) F)) -> (Eq.{succ u1} S (f (Filter.liminfₛ.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} R _inst_2))) F)) (Filter.limsup.{u1, u2} S R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} S (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} S (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u1} S _inst_5))) f F))
Case conversion may be inaccurate. Consider using '#align antitone.map_Liminf_of_continuous_at Antitone.map_liminfₛ_of_continuousAtₓ'. -/
/-- An antitone function between complete linear ordered spaces sends a `filter.Liminf`
to the `filter.limsup` of the image if it is continuous at the `Liminf`. -/
theorem Antitone.map_liminfₛ_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.liminfₛ) : f F.liminfₛ = F.limsup f :=
  @Antitone.map_limsupₛ_of_continuousAt (OrderDual R) (OrderDual S) _ _ _ _ _ _ _ _ f f_decr.dual
    f_cont
#align antitone.map_Liminf_of_continuous_at Antitone.map_liminfₛ_of_continuousAt

/- warning: antitone.map_liminf_of_continuous_at -> Antitone.map_liminf_of_continuousAt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} {F : Filter.{u1} ι} [_inst_1 : Filter.NeBot.{u1} ι F] [_inst_2 : CompleteLinearOrder.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : OrderTopology.{u2} R _inst_3 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u3} S] [_inst_6 : TopologicalSpace.{u3} S] [_inst_7 : OrderTopology.{u3} S _inst_6 (PartialOrder.toPreorder.{u3} S (CompleteSemilatticeInf.toPartialOrder.{u3} S (CompleteLattice.toCompleteSemilatticeInf.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5))))] {f : R -> S}, (Antitone.{u2, u3} R S (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (PartialOrder.toPreorder.{u3} S (CompleteSemilatticeInf.toPartialOrder.{u3} S (CompleteLattice.toCompleteSemilatticeInf.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5)))) f) -> (forall (a : ι -> R), (ContinuousAt.{u2, u3} R S _inst_3 _inst_6 f (Filter.liminf.{u2, u1} R ι (CompleteLattice.toConditionallyCompleteLattice.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)) a F)) -> (Eq.{succ u3} S (f (Filter.liminf.{u2, u1} R ι (CompleteLattice.toConditionallyCompleteLattice.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)) a F)) (Filter.limsup.{u3, u1} S ι (CompleteLattice.toConditionallyCompleteLattice.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5)) (Function.comp.{succ u1, succ u2, succ u3} ι R S f a) F)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} {F : Filter.{u1} ι} [_inst_1 : Filter.NeBot.{u1} ι F] [_inst_2 : CompleteLinearOrder.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_4 : OrderTopology.{u3} R _inst_3 (PartialOrder.toPreorder.{u3} R (CompleteSemilatticeInf.toPartialOrder.{u3} R (CompleteLattice.toCompleteSemilatticeInf.{u3} R (CompleteLinearOrder.toCompleteLattice.{u3} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u2} S] [_inst_6 : TopologicalSpace.{u2} S] [_inst_7 : OrderTopology.{u2} S _inst_6 (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5))))] {f : R -> S}, (Antitone.{u3, u2} R S (PartialOrder.toPreorder.{u3} R (CompleteSemilatticeInf.toPartialOrder.{u3} R (CompleteLattice.toCompleteSemilatticeInf.{u3} R (CompleteLinearOrder.toCompleteLattice.{u3} R _inst_2)))) (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)))) f) -> (forall (a : ι -> R), (ContinuousAt.{u3, u2} R S _inst_3 _inst_6 f (Filter.liminf.{u3, u1} R ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u3} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u3} R _inst_2))) a F)) -> (Eq.{succ u2} S (f (Filter.liminf.{u3, u1} R ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u3} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u3} R _inst_2))) a F)) (Filter.limsup.{u2, u1} S ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} S (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} S (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} S _inst_5))) (Function.comp.{succ u1, succ u3, succ u2} ι R S f a) F)))
Case conversion may be inaccurate. Consider using '#align antitone.map_liminf_of_continuous_at Antitone.map_liminf_of_continuousAtₓ'. -/
/-- A continuous antitone function between complete linear ordered spaces sends a `filter.liminf`
to the `filter.limsup` of the images. -/
theorem Antitone.map_liminf_of_continuousAt {f : R → S} (f_decr : Antitone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.liminf a)) : f (F.liminf a) = F.limsup (f ∘ a) :=
  f_decr.map_liminfₛ_of_continuousAt f_cont
#align antitone.map_liminf_of_continuous_at Antitone.map_liminf_of_continuousAt

/- warning: monotone.map_Limsup_of_continuous_at -> Monotone.map_limsupₛ_of_continuousAt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : CompleteLinearOrder.{u1} R] [_inst_3 : TopologicalSpace.{u1} R] [_inst_4 : OrderTopology.{u1} R _inst_3 (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u2} S] [_inst_6 : TopologicalSpace.{u2} S] [_inst_7 : OrderTopology.{u2} S _inst_6 (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5))))] {F : Filter.{u1} R} [_inst_8 : Filter.NeBot.{u1} R F] {f : R -> S}, (Monotone.{u1, u2} R S (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)))) f) -> (ContinuousAt.{u1, u2} R S _inst_3 _inst_6 f (Filter.limsupₛ.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) F)) -> (Eq.{succ u2} S (f (Filter.limsupₛ.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) F)) (Filter.limsup.{u2, u1} S R (CompleteLattice.toConditionallyCompleteLattice.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)) f F))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_2 : CompleteLinearOrder.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : OrderTopology.{u2} R _inst_3 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u1} S] [_inst_6 : TopologicalSpace.{u1} S] [_inst_7 : OrderTopology.{u1} S _inst_6 (PartialOrder.toPreorder.{u1} S (CompleteSemilatticeInf.toPartialOrder.{u1} S (CompleteLattice.toCompleteSemilatticeInf.{u1} S (CompleteLinearOrder.toCompleteLattice.{u1} S _inst_5))))] {F : Filter.{u2} R} [_inst_8 : Filter.NeBot.{u2} R F] {f : R -> S}, (Monotone.{u2, u1} R S (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (PartialOrder.toPreorder.{u1} S (CompleteSemilatticeInf.toPartialOrder.{u1} S (CompleteLattice.toCompleteSemilatticeInf.{u1} S (CompleteLinearOrder.toCompleteLattice.{u1} S _inst_5)))) f) -> (ContinuousAt.{u2, u1} R S _inst_3 _inst_6 f (Filter.limsupₛ.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} R _inst_2))) F)) -> (Eq.{succ u1} S (f (Filter.limsupₛ.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} R _inst_2))) F)) (Filter.limsup.{u1, u2} S R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} S (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} S (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u1} S _inst_5))) f F))
Case conversion may be inaccurate. Consider using '#align monotone.map_Limsup_of_continuous_at Monotone.map_limsupₛ_of_continuousAtₓ'. -/
/-- A monotone function between complete linear ordered spaces sends a `filter.Limsup`
to the `filter.limsup` of the image if it is continuous at the `Limsup`. -/
theorem Monotone.map_limsupₛ_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsupₛ) : f F.limsupₛ = F.limsup f :=
  @Antitone.map_limsupₛ_of_continuousAt R (OrderDual S) _ _ _ _ _ _ _ _ f f_incr f_cont
#align monotone.map_Limsup_of_continuous_at Monotone.map_limsupₛ_of_continuousAt

/- warning: monotone.map_limsup_of_continuous_at -> Monotone.map_limsup_of_continuousAt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} {F : Filter.{u1} ι} [_inst_1 : Filter.NeBot.{u1} ι F] [_inst_2 : CompleteLinearOrder.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : OrderTopology.{u2} R _inst_3 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u3} S] [_inst_6 : TopologicalSpace.{u3} S] [_inst_7 : OrderTopology.{u3} S _inst_6 (PartialOrder.toPreorder.{u3} S (CompleteSemilatticeInf.toPartialOrder.{u3} S (CompleteLattice.toCompleteSemilatticeInf.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5))))] {f : R -> S}, (Monotone.{u2, u3} R S (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (PartialOrder.toPreorder.{u3} S (CompleteSemilatticeInf.toPartialOrder.{u3} S (CompleteLattice.toCompleteSemilatticeInf.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5)))) f) -> (forall (a : ι -> R), (ContinuousAt.{u2, u3} R S _inst_3 _inst_6 f (Filter.limsup.{u2, u1} R ι (CompleteLattice.toConditionallyCompleteLattice.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)) a F)) -> (Eq.{succ u3} S (f (Filter.limsup.{u2, u1} R ι (CompleteLattice.toConditionallyCompleteLattice.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)) a F)) (Filter.limsup.{u3, u1} S ι (CompleteLattice.toConditionallyCompleteLattice.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5)) (Function.comp.{succ u1, succ u2, succ u3} ι R S f a) F)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} {F : Filter.{u1} ι} [_inst_1 : Filter.NeBot.{u1} ι F] [_inst_2 : CompleteLinearOrder.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_4 : OrderTopology.{u3} R _inst_3 (PartialOrder.toPreorder.{u3} R (CompleteSemilatticeInf.toPartialOrder.{u3} R (CompleteLattice.toCompleteSemilatticeInf.{u3} R (CompleteLinearOrder.toCompleteLattice.{u3} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u2} S] [_inst_6 : TopologicalSpace.{u2} S] [_inst_7 : OrderTopology.{u2} S _inst_6 (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5))))] {f : R -> S}, (Monotone.{u3, u2} R S (PartialOrder.toPreorder.{u3} R (CompleteSemilatticeInf.toPartialOrder.{u3} R (CompleteLattice.toCompleteSemilatticeInf.{u3} R (CompleteLinearOrder.toCompleteLattice.{u3} R _inst_2)))) (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)))) f) -> (forall (a : ι -> R), (ContinuousAt.{u3, u2} R S _inst_3 _inst_6 f (Filter.limsup.{u3, u1} R ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u3} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u3} R _inst_2))) a F)) -> (Eq.{succ u2} S (f (Filter.limsup.{u3, u1} R ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u3} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u3} R _inst_2))) a F)) (Filter.limsup.{u2, u1} S ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} S (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} S (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} S _inst_5))) (Function.comp.{succ u1, succ u3, succ u2} ι R S f a) F)))
Case conversion may be inaccurate. Consider using '#align monotone.map_limsup_of_continuous_at Monotone.map_limsup_of_continuousAtₓ'. -/
/-- A continuous monotone function between complete linear ordered spaces sends a `filter.limsup`
to the `filter.limsup` of the images. -/
theorem Monotone.map_limsup_of_continuousAt {f : R → S} (f_incr : Monotone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.limsup a)) : f (F.limsup a) = F.limsup (f ∘ a) :=
  f_incr.map_limsupₛ_of_continuousAt f_cont
#align monotone.map_limsup_of_continuous_at Monotone.map_limsup_of_continuousAt

/- warning: monotone.map_Liminf_of_continuous_at -> Monotone.map_liminfₛ_of_continuousAt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : CompleteLinearOrder.{u1} R] [_inst_3 : TopologicalSpace.{u1} R] [_inst_4 : OrderTopology.{u1} R _inst_3 (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u2} S] [_inst_6 : TopologicalSpace.{u2} S] [_inst_7 : OrderTopology.{u2} S _inst_6 (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5))))] {F : Filter.{u1} R} [_inst_8 : Filter.NeBot.{u1} R F] {f : R -> S}, (Monotone.{u1, u2} R S (PartialOrder.toPreorder.{u1} R (CompleteSemilatticeInf.toPartialOrder.{u1} R (CompleteLattice.toCompleteSemilatticeInf.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)))) (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)))) f) -> (ContinuousAt.{u1, u2} R S _inst_3 _inst_6 f (Filter.liminfₛ.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) F)) -> (Eq.{succ u2} S (f (Filter.liminfₛ.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R (CompleteLinearOrder.toCompleteLattice.{u1} R _inst_2)) F)) (Filter.liminf.{u2, u1} S R (CompleteLattice.toConditionallyCompleteLattice.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)) f F))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_2 : CompleteLinearOrder.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : OrderTopology.{u2} R _inst_3 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u1} S] [_inst_6 : TopologicalSpace.{u1} S] [_inst_7 : OrderTopology.{u1} S _inst_6 (PartialOrder.toPreorder.{u1} S (CompleteSemilatticeInf.toPartialOrder.{u1} S (CompleteLattice.toCompleteSemilatticeInf.{u1} S (CompleteLinearOrder.toCompleteLattice.{u1} S _inst_5))))] {F : Filter.{u2} R} [_inst_8 : Filter.NeBot.{u2} R F] {f : R -> S}, (Monotone.{u2, u1} R S (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (PartialOrder.toPreorder.{u1} S (CompleteSemilatticeInf.toPartialOrder.{u1} S (CompleteLattice.toCompleteSemilatticeInf.{u1} S (CompleteLinearOrder.toCompleteLattice.{u1} S _inst_5)))) f) -> (ContinuousAt.{u2, u1} R S _inst_3 _inst_6 f (Filter.liminfₛ.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} R _inst_2))) F)) -> (Eq.{succ u1} S (f (Filter.liminfₛ.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} R _inst_2))) F)) (Filter.liminf.{u1, u2} S R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} S (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} S (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u1} S _inst_5))) f F))
Case conversion may be inaccurate. Consider using '#align monotone.map_Liminf_of_continuous_at Monotone.map_liminfₛ_of_continuousAtₓ'. -/
/-- A monotone function between complete linear ordered spaces sends a `filter.Liminf`
to the `filter.liminf` of the image if it is continuous at the `Liminf`. -/
theorem Monotone.map_liminfₛ_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.liminfₛ) : f F.liminfₛ = F.liminf f :=
  @Antitone.map_liminfₛ_of_continuousAt R (OrderDual S) _ _ _ _ _ _ _ _ f f_incr f_cont
#align monotone.map_Liminf_of_continuous_at Monotone.map_liminfₛ_of_continuousAt

/- warning: monotone.map_liminf_of_continuous_at -> Monotone.map_liminf_of_continuousAt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} {F : Filter.{u1} ι} [_inst_1 : Filter.NeBot.{u1} ι F] [_inst_2 : CompleteLinearOrder.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : OrderTopology.{u2} R _inst_3 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u3} S] [_inst_6 : TopologicalSpace.{u3} S] [_inst_7 : OrderTopology.{u3} S _inst_6 (PartialOrder.toPreorder.{u3} S (CompleteSemilatticeInf.toPartialOrder.{u3} S (CompleteLattice.toCompleteSemilatticeInf.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5))))] {f : R -> S}, (Monotone.{u2, u3} R S (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)))) (PartialOrder.toPreorder.{u3} S (CompleteSemilatticeInf.toPartialOrder.{u3} S (CompleteLattice.toCompleteSemilatticeInf.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5)))) f) -> (forall (a : ι -> R), (ContinuousAt.{u2, u3} R S _inst_3 _inst_6 f (Filter.liminf.{u2, u1} R ι (CompleteLattice.toConditionallyCompleteLattice.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)) a F)) -> (Eq.{succ u3} S (f (Filter.liminf.{u2, u1} R ι (CompleteLattice.toConditionallyCompleteLattice.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_2)) a F)) (Filter.liminf.{u3, u1} S ι (CompleteLattice.toConditionallyCompleteLattice.{u3} S (CompleteLinearOrder.toCompleteLattice.{u3} S _inst_5)) (Function.comp.{succ u1, succ u2, succ u3} ι R S f a) F)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} {F : Filter.{u1} ι} [_inst_1 : Filter.NeBot.{u1} ι F] [_inst_2 : CompleteLinearOrder.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_4 : OrderTopology.{u3} R _inst_3 (PartialOrder.toPreorder.{u3} R (CompleteSemilatticeInf.toPartialOrder.{u3} R (CompleteLattice.toCompleteSemilatticeInf.{u3} R (CompleteLinearOrder.toCompleteLattice.{u3} R _inst_2))))] [_inst_5 : CompleteLinearOrder.{u2} S] [_inst_6 : TopologicalSpace.{u2} S] [_inst_7 : OrderTopology.{u2} S _inst_6 (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5))))] {f : R -> S}, (Monotone.{u3, u2} R S (PartialOrder.toPreorder.{u3} R (CompleteSemilatticeInf.toPartialOrder.{u3} R (CompleteLattice.toCompleteSemilatticeInf.{u3} R (CompleteLinearOrder.toCompleteLattice.{u3} R _inst_2)))) (PartialOrder.toPreorder.{u2} S (CompleteSemilatticeInf.toPartialOrder.{u2} S (CompleteLattice.toCompleteSemilatticeInf.{u2} S (CompleteLinearOrder.toCompleteLattice.{u2} S _inst_5)))) f) -> (forall (a : ι -> R), (ContinuousAt.{u3, u2} R S _inst_3 _inst_6 f (Filter.liminf.{u3, u1} R ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u3} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u3} R _inst_2))) a F)) -> (Eq.{succ u2} S (f (Filter.liminf.{u3, u1} R ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u3} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u3} R _inst_2))) a F)) (Filter.liminf.{u2, u1} S ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} S (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} S (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} S _inst_5))) (Function.comp.{succ u1, succ u3, succ u2} ι R S f a) F)))
Case conversion may be inaccurate. Consider using '#align monotone.map_liminf_of_continuous_at Monotone.map_liminf_of_continuousAtₓ'. -/
/-- A continuous monotone function between complete linear ordered spaces sends a `filter.liminf`
to the `filter.liminf` of the images. -/
theorem Monotone.map_liminf_of_continuousAt {f : R → S} (f_incr : Monotone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.liminf a)) : f (F.liminf a) = F.liminf (f ∘ a) :=
  f_incr.map_liminfₛ_of_continuousAt f_cont
#align monotone.map_liminf_of_continuous_at Monotone.map_liminf_of_continuousAt

end Monotone

section InfiAndSupr

open Topology

open Filter Set

variable {ι : Type _} {R : Type _} [CompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]

/- warning: infi_eq_of_forall_le_of_tendsto -> infᵢ_eq_of_forall_le_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CompleteLinearOrder.{u2} R] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : OrderTopology.{u2} R _inst_2 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_1))))] {x : R} {as : ι -> R}, (forall (i : ι), LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_1))))) x (as i)) -> (forall {F : Filter.{u1} ι} [_inst_4 : Filter.NeBot.{u1} ι F], (Filter.Tendsto.{u1, u2} ι R as F (nhds.{u2} R _inst_2 x)) -> (Eq.{succ u2} R (infᵢ.{u2, succ u1} R (ConditionallyCompleteLattice.toHasInf.{u2} R (CompleteLattice.toConditionallyCompleteLattice.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_1))) ι (fun (i : ι) => as i)) x))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CompleteLinearOrder.{u2} R] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : OrderTopology.{u2} R _inst_2 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_1))))] {x : R} {as : ι -> R}, (forall (i : ι), LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_1))))) x (as i)) -> (forall {F : Filter.{u1} ι} [_inst_4 : Filter.NeBot.{u1} ι F], (Filter.Tendsto.{u1, u2} ι R as F (nhds.{u2} R _inst_2 x)) -> (Eq.{succ u2} R (infᵢ.{u2, succ u1} R (ConditionallyCompleteLattice.toInfSet.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} R _inst_1)))) ι (fun (i : ι) => as i)) x))
Case conversion may be inaccurate. Consider using '#align infi_eq_of_forall_le_of_tendsto infᵢ_eq_of_forall_le_of_tendstoₓ'. -/
theorem infᵢ_eq_of_forall_le_of_tendsto {x : R} {as : ι → R} (x_le : ∀ i, x ≤ as i) {F : Filter ι}
    [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) : (⨅ i, as i) = x :=
  by
  refine' infᵢ_eq_of_forall_ge_of_forall_gt_exists_lt (fun i => x_le i) _
  apply fun w x_lt_w => ‹Filter.NeBot F›.nonempty_of_mem (eventually_lt_of_tendsto_lt x_lt_w as_lim)
#align infi_eq_of_forall_le_of_tendsto infᵢ_eq_of_forall_le_of_tendsto

/- warning: supr_eq_of_forall_le_of_tendsto -> supᵢ_eq_of_forall_le_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CompleteLinearOrder.{u2} R] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : OrderTopology.{u2} R _inst_2 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_1))))] {x : R} {as : ι -> R}, (forall (i : ι), LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_1))))) (as i) x) -> (forall {F : Filter.{u1} ι} [_inst_4 : Filter.NeBot.{u1} ι F], (Filter.Tendsto.{u1, u2} ι R as F (nhds.{u2} R _inst_2 x)) -> (Eq.{succ u2} R (supᵢ.{u2, succ u1} R (ConditionallyCompleteLattice.toHasSup.{u2} R (CompleteLattice.toConditionallyCompleteLattice.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_1))) ι (fun (i : ι) => as i)) x))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CompleteLinearOrder.{u2} R] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : OrderTopology.{u2} R _inst_2 (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_1))))] {x : R} {as : ι -> R}, (forall (i : ι), LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (CompleteSemilatticeInf.toPartialOrder.{u2} R (CompleteLattice.toCompleteSemilatticeInf.{u2} R (CompleteLinearOrder.toCompleteLattice.{u2} R _inst_1))))) (as i) x) -> (forall {F : Filter.{u1} ι} [_inst_4 : Filter.NeBot.{u1} ι F], (Filter.Tendsto.{u1, u2} ι R as F (nhds.{u2} R _inst_2 x)) -> (Eq.{succ u2} R (supᵢ.{u2, succ u1} R (ConditionallyCompleteLattice.toSupSet.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} R (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} R _inst_1)))) ι (fun (i : ι) => as i)) x))
Case conversion may be inaccurate. Consider using '#align supr_eq_of_forall_le_of_tendsto supᵢ_eq_of_forall_le_of_tendstoₓ'. -/
theorem supᵢ_eq_of_forall_le_of_tendsto {x : R} {as : ι → R} (le_x : ∀ i, as i ≤ x) {F : Filter ι}
    [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) : (⨆ i, as i) = x :=
  @infᵢ_eq_of_forall_le_of_tendsto ι (OrderDual R) _ _ _ x as le_x F _ as_lim
#align supr_eq_of_forall_le_of_tendsto supᵢ_eq_of_forall_le_of_tendsto

#print unionᵢ_Ici_eq_Ioi_of_lt_of_tendsto /-
theorem unionᵢ_Ici_eq_Ioi_of_lt_of_tendsto {ι : Type _} (x : R) {as : ι → R} (x_lt : ∀ i, x < as i)
    {F : Filter ι} [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) :
    (⋃ i : ι, Ici (as i)) = Ioi x :=
  by
  have obs : x ∉ range as := by
    intro maybe_x_is
    rcases mem_range.mp maybe_x_is with ⟨i, hi⟩
    simpa only [hi, lt_self_iff_false] using x_lt i
  rw [← infᵢ_eq_of_forall_le_of_tendsto (fun i => (x_lt i).le) as_lim] at *
  exact unionᵢ_Ici_eq_Ioi_infᵢ obs
#align Union_Ici_eq_Ioi_of_lt_of_tendsto unionᵢ_Ici_eq_Ioi_of_lt_of_tendsto
-/

#print unionᵢ_Iic_eq_Iio_of_lt_of_tendsto /-
theorem unionᵢ_Iic_eq_Iio_of_lt_of_tendsto {ι : Type _} (x : R) {as : ι → R} (lt_x : ∀ i, as i < x)
    {F : Filter ι} [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) :
    (⋃ i : ι, Iic (as i)) = Iio x :=
  @unionᵢ_Ici_eq_Ioi_of_lt_of_tendsto (OrderDual R) _ _ _ ι x as lt_x F _ as_lim
#align Union_Iic_eq_Iio_of_lt_of_tendsto unionᵢ_Iic_eq_Iio_of_lt_of_tendsto
-/

end InfiAndSupr

section Indicator

open BigOperators

/- warning: limsup_eq_tendsto_sum_indicator_nat_at_top -> limsup_eq_tendsto_sum_indicator_nat_atTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Nat -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Filter.limsup.{u1, 0} (Set.{u1} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (setOf.{u1} α (fun (ω : α) => Filter.Tendsto.{0, 0} Nat Nat (fun (n : Nat) => Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.range n) (fun (k : Nat) => Set.indicator.{u1, 0} α Nat Nat.hasZero (s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{u1} (α -> Nat) 1 (OfNat.mk.{u1} (α -> Nat) 1 (One.one.{u1} (α -> Nat) (Pi.instOne.{u1, 0} α (fun (ᾰ : α) => Nat) (fun (i : α) => Nat.hasOne))))) ω)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))))
but is expected to have type
  forall {α : Type.{u1}} (s : Nat -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Filter.limsup.{u1, 0} (Set.{u1} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (setOf.{u1} α (fun (ω : α) => Filter.Tendsto.{0, 0} Nat Nat (fun (n : Nat) => Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.range n) (fun (k : Nat) => Set.indicator.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (OfNat.ofNat.{u1} (α -> Nat) 1 (One.toOfNat1.{u1} (α -> Nat) (Pi.instOne.{u1, 0} α (fun (a._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.4450 : α) => Nat) (fun (i : α) => CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)))) ω)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))))
Case conversion may be inaccurate. Consider using '#align limsup_eq_tendsto_sum_indicator_nat_at_top limsup_eq_tendsto_sum_indicator_nat_atTopₓ'. -/
theorem limsup_eq_tendsto_sum_indicator_nat_atTop (s : ℕ → Set α) :
    limsup s atTop =
      { ω |
        Tendsto (fun n => ∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → ℕ) ω) atTop
          atTop } :=
  by
  ext ω
  simp only [limsup_eq_infi_supr_of_nat, ge_iff_le, Set.supᵢ_eq_unionᵢ, Set.infᵢ_eq_interᵢ,
    Set.mem_interᵢ, Set.mem_unionᵢ, exists_prop]
  constructor
  · intro hω
    refine'
      tendsto_at_top_at_top_of_monotone'
        (fun n m hnm =>
          Finset.sum_mono_set_of_nonneg (fun i => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
            (Finset.range_mono hnm))
        _
    rintro ⟨i, h⟩
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff'] at h
    induction' i with k hk
    · obtain ⟨j, hj₁, hj₂⟩ := hω 1
      refine'
        not_lt.2 (h <| j + 1)
          (lt_of_le_of_lt (finset.sum_const_zero.symm : 0 = ∑ k in Finset.range (j + 1), 0).le _)
      refine'
        Finset.sum_lt_sum (fun m _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
          ⟨j - 1, Finset.mem_range.2 (lt_of_le_of_lt (Nat.sub_le _ _) j.lt_succ_self), _⟩
      rw [Nat.sub_add_cancel hj₁, Set.indicator_of_mem hj₂]
      exact zero_lt_one
    · rw [imp_false] at hk
      push_neg  at hk
      obtain ⟨i, hi⟩ := hk
      obtain ⟨j, hj₁, hj₂⟩ := hω (i + 1)
      replace hi : (∑ k in Finset.range i, (s (k + 1)).indicator 1 ω) = k + 1 :=
        le_antisymm (h i) hi
      refine' not_lt.2 (h <| j + 1) _
      rw [← Finset.sum_range_add_sum_Ico _ (i.le_succ.trans (hj₁.trans j.le_succ)), hi]
      refine' lt_add_of_pos_right _ _
      rw [(finset.sum_const_zero.symm : 0 = ∑ k in Finset.Ico i (j + 1), 0)]
      refine'
        Finset.sum_lt_sum (fun m _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
          ⟨j - 1,
            Finset.mem_Ico.2
              ⟨(Nat.le_sub_iff_right (le_trans ((le_add_iff_nonneg_left _).2 zero_le') hj₁)).2 hj₁,
                lt_of_le_of_lt (Nat.sub_le _ _) j.lt_succ_self⟩,
            _⟩
      rw [Nat.sub_add_cancel (le_trans ((le_add_iff_nonneg_left _).2 zero_le') hj₁),
        Set.indicator_of_mem hj₂]
      exact zero_lt_one
  · rintro hω i
    rw [Set.mem_setOf_eq, tendsto_at_top_at_top] at hω
    by_contra hcon
    push_neg  at hcon
    obtain ⟨j, h⟩ := hω (i + 1)
    have : (∑ k in Finset.range j, (s (k + 1)).indicator 1 ω) ≤ i :=
      by
      have hle : ∀ j ≤ i, (∑ k in Finset.range j, (s (k + 1)).indicator 1 ω) ≤ i :=
        by
        refine' fun j hij =>
          (Finset.sum_le_card_nsmul _ _ _ _ : _ ≤ (Finset.range j).card • 1).trans _
        · exact fun m hm => Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
        · simpa only [Finset.card_range, smul_eq_mul, mul_one]
      by_cases hij : j < i
      · exact hle _ hij.le
      · rw [← Finset.sum_range_add_sum_Ico _ (not_lt.1 hij)]
        suffices (∑ k in Finset.Ico i j, (s (k + 1)).indicator 1 ω) = 0
          by
          rw [this, add_zero]
          exact hle _ le_rfl
        rw [Finset.sum_eq_zero fun m hm => _]
        exact Set.indicator_of_not_mem (hcon _ <| (Finset.mem_Ico.1 hm).1.trans m.le_succ) _
    exact not_le.2 (lt_of_lt_of_le i.lt_succ_self <| h _ le_rfl) this
#align limsup_eq_tendsto_sum_indicator_nat_at_top limsup_eq_tendsto_sum_indicator_nat_atTop

/- warning: limsup_eq_tendsto_sum_indicator_at_top -> limsup_eq_tendsto_sum_indicator_atTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (R : Type.{u2}) [_inst_1 : StrictOrderedSemiring.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R _inst_1))] (s : Nat -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Filter.limsup.{u1, 0} (Set.{u1} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (setOf.{u1} α (fun (ω : α) => Filter.Tendsto.{0, u2} Nat R (fun (n : Nat) => Finset.sum.{u2, 0} R Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} R _inst_1)) (Finset.range n) (fun (k : Nat) => Set.indicator.{u1, u2} α R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R _inst_1))))) (s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{max u1 u2} (α -> R) 1 (OfNat.mk.{max u1 u2} (α -> R) 1 (One.one.{max u1 u2} (α -> R) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => AddMonoidWithOne.toOne.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R _inst_1))))))))) ω)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} R _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} (R : Type.{u1}) [_inst_1 : StrictOrderedSemiring.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R _inst_1))] (s : Nat -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Filter.limsup.{u2, 0} (Set.{u2} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (setOf.{u2} α (fun (ω : α) => Filter.Tendsto.{0, u1} Nat R (fun (n : Nat) => Finset.sum.{u1, 0} R Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1)))) (Finset.range n) (fun (k : Nat) => Set.indicator.{u2, u1} α R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1))) (s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (OfNat.ofNat.{max u2 u1} (α -> R) 1 (One.toOfNat1.{max u2 u1} (α -> R) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Topology.Algebra.Order.LiminfLimsup._hyg.5390 : α) => R) (fun (i : α) => Semiring.toOne.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1))))) ω)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (Filter.atTop.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedSemiring.toPartialOrder.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align limsup_eq_tendsto_sum_indicator_at_top limsup_eq_tendsto_sum_indicator_atTopₓ'. -/
theorem limsup_eq_tendsto_sum_indicator_atTop (R : Type _) [StrictOrderedSemiring R] [Archimedean R]
    (s : ℕ → Set α) :
    limsup s atTop =
      { ω |
        Tendsto (fun n => ∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → R) ω) atTop
          atTop } :=
  by
  rw [limsup_eq_tendsto_sum_indicator_nat_atTop s]
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [(_ :
      (fun n => ∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → R) ω) = fun n =>
        ↑(∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → ℕ) ω))]
  · exact tendsto_coe_nat_at_top_iff.symm
  · ext n
    simp only [Set.indicator, Pi.one_apply, Finset.sum_boole, Nat.cast_id]
#align limsup_eq_tendsto_sum_indicator_at_top limsup_eq_tendsto_sum_indicator_atTop

end Indicator

