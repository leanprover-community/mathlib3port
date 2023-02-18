/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.monotone_convergence
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order.Basic

/-!
# Bounded monotone sequences converge

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove a few theorems of the form “if the range of a monotone function `f : ι → α`
admits a least upper bound `a`, then `f x` tends to `a` as `x → ∞`”, as well as version of this
statement for (conditionally) complete lattices that use `⨆ x, f x` instead of `is_lub`.

These theorems work for linear orders with order topologies as well as their products (both in terms
of `prod` and in terms of function types). In order to reduce code duplication, we introduce two
typeclasses (one for the property formulated above and one for the dual property), prove theorems
assuming one of these typeclasses, and provide instances for linear orders and their products.

We also prove some "inverse" results: if `f n` is a monotone sequence and `a` is its limit,
then `f n ≤ a` for all `n`.

## Tags

monotone convergence
-/


open Filter Set Function

open Filter Topology Classical

variable {α β : Type _}

#print SupConvergenceClass /-
/-- We say that `α` is a `Sup_convergence_class` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a least upper bound of `set.range f`. Then `f x` tends to `𝓝 a` as
`x → ∞` (formally, at the filter `filter.at_top`). We require this for `ι = (s : set α)`, `f = coe`
in the definition, then prove it for any `f` in `tendsto_at_top_is_lub`.

This property holds for linear orders with order topology as well as their products. -/
class SupConvergenceClass (α : Type _) [Preorder α] [TopologicalSpace α] : Prop where
  tendsto_coe_atTop_isLUB : ∀ (a : α) (s : Set α), IsLUB s a → Tendsto (coe : s → α) atTop (𝓝 a)
#align Sup_convergence_class SupConvergenceClass
-/

#print InfConvergenceClass /-
/-- We say that `α` is an `Inf_convergence_class` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a greatest lower bound of `set.range f`. Then `f x` tends to `𝓝 a`
as `x → -∞` (formally, at the filter `filter.at_bot`). We require this for `ι = (s : set α)`,
`f = coe` in the definition, then prove it for any `f` in `tendsto_at_bot_is_glb`.

This property holds for linear orders with order topology as well as their products. -/
class InfConvergenceClass (α : Type _) [Preorder α] [TopologicalSpace α] : Prop where
  tendsto_coe_atBot_isGLB : ∀ (a : α) (s : Set α), IsGLB s a → Tendsto (coe : s → α) atBot (𝓝 a)
#align Inf_convergence_class InfConvergenceClass
-/

#print OrderDual.supConvergenceClass /-
instance OrderDual.supConvergenceClass [Preorder α] [TopologicalSpace α] [InfConvergenceClass α] :
    SupConvergenceClass αᵒᵈ :=
  ⟨‹InfConvergenceClass α›.1⟩
#align order_dual.Sup_convergence_class OrderDual.supConvergenceClass
-/

#print OrderDual.infConvergenceClass /-
instance OrderDual.infConvergenceClass [Preorder α] [TopologicalSpace α] [SupConvergenceClass α] :
    InfConvergenceClass αᵒᵈ :=
  ⟨‹SupConvergenceClass α›.1⟩
#align order_dual.Inf_convergence_class OrderDual.infConvergenceClass
-/

#print LinearOrder.supConvergenceClass /-
-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.supConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : SupConvergenceClass α :=
  by
  refine' ⟨fun a s ha => tendsto_order.2 ⟨fun b hb => _, fun b hb => _⟩⟩
  · rcases ha.exists_between hb with ⟨c, hcs, bc, bca⟩
    lift c to s using hcs
    refine' (eventually_ge_at_top c).mono fun x hx => bc.trans_le hx
  · exact eventually_of_forall fun x => (ha.1 x.2).trans_lt hb
#align linear_order.Sup_convergence_class LinearOrder.supConvergenceClass
-/

#print LinearOrder.infConvergenceClass /-
-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.infConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : InfConvergenceClass α :=
  show InfConvergenceClass αᵒᵈᵒᵈ from OrderDual.infConvergenceClass
#align linear_order.Inf_convergence_class LinearOrder.infConvergenceClass
-/

section

variable {ι : Type _} [Preorder ι] [TopologicalSpace α]

section IsLUB

variable [Preorder α] [SupConvergenceClass α] {f : ι → α} {a : α}

#print tendsto_atTop_isLUB /-
theorem tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) :=
  by
  suffices : tendsto (range_factorization f) at_top at_top
  exact (SupConvergenceClass.tendsto_coe_atTop_isLUB _ _ ha).comp this
  exact h_mono.range_factorization.tendsto_at_top_at_top fun b => b.2.imp fun a ha => ha.ge
#align tendsto_at_top_is_lub tendsto_atTop_isLUB
-/

#print tendsto_atBot_isLUB /-
theorem tendsto_atBot_isLUB (h_anti : Antitone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert tendsto_atTop_isLUB h_anti.dual_left ha
#align tendsto_at_bot_is_lub tendsto_atBot_isLUB
-/

end IsLUB

section IsGLB

variable [Preorder α] [InfConvergenceClass α] {f : ι → α} {a : α}

#print tendsto_atBot_isGLB /-
theorem tendsto_atBot_isGLB (h_mono : Monotone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert tendsto_atTop_isLUB h_mono.dual ha.dual
#align tendsto_at_bot_is_glb tendsto_atBot_isGLB
-/

#print tendsto_atTop_isGLB /-
theorem tendsto_atTop_isGLB (h_anti : Antitone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by convert tendsto_atBot_isLUB h_anti.dual ha.dual
#align tendsto_at_top_is_glb tendsto_atTop_isGLB
-/

end IsGLB

section Csupr

variable [ConditionallyCompleteLattice α] [SupConvergenceClass α] {f : ι → α} {a : α}

/- warning: tendsto_at_top_csupr -> tendsto_atTop_csupr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : SupConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) _inst_2] {f : ι -> α}, (Monotone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) f) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) (Set.range.{u1, succ u2} α ι f)) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atTop.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_3) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : SupConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) _inst_2] {f : ι -> α}, (Monotone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) f) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) (Set.range.{u1, succ u2} α ι f)) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atTop.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_3) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align tendsto_at_top_csupr tendsto_atTop_csuprₓ'. -/
theorem tendsto_atTop_csupr (h_mono : Monotone f) (hbdd : BddAbove <| range f) :
    Tendsto f atTop (𝓝 (⨆ i, f i)) :=
  by
  cases isEmpty_or_nonempty ι
  exacts[tendsto_of_is_empty, tendsto_atTop_isLUB h_mono (isLUB_csupᵢ hbdd)]
#align tendsto_at_top_csupr tendsto_atTop_csupr

/- warning: tendsto_at_bot_csupr -> tendsto_atBot_csupr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : SupConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) _inst_2] {f : ι -> α}, (Antitone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) f) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) (Set.range.{u1, succ u2} α ι f)) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atBot.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_3) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : SupConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) _inst_2] {f : ι -> α}, (Antitone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) f) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) (Set.range.{u1, succ u2} α ι f)) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atBot.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_3) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align tendsto_at_bot_csupr tendsto_atBot_csuprₓ'. -/
theorem tendsto_atBot_csupr (h_anti : Antitone f) (hbdd : BddAbove <| range f) :
    Tendsto f atBot (𝓝 (⨆ i, f i)) := by convert tendsto_atTop_csupr h_anti.dual hbdd.dual
#align tendsto_at_bot_csupr tendsto_atBot_csupr

end Csupr

section Cinfi

variable [ConditionallyCompleteLattice α] [InfConvergenceClass α] {f : ι → α} {a : α}

/- warning: tendsto_at_bot_cinfi -> tendsto_atBot_cinfi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : InfConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) _inst_2] {f : ι -> α}, (Monotone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) f) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) (Set.range.{u1, succ u2} α ι f)) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atBot.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_3) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : InfConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) _inst_2] {f : ι -> α}, (Monotone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) f) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) (Set.range.{u1, succ u2} α ι f)) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atBot.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_3) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align tendsto_at_bot_cinfi tendsto_atBot_cinfiₓ'. -/
theorem tendsto_atBot_cinfi (h_mono : Monotone f) (hbdd : BddBelow <| range f) :
    Tendsto f atBot (𝓝 (⨅ i, f i)) := by convert tendsto_atTop_csupr h_mono.dual hbdd.dual
#align tendsto_at_bot_cinfi tendsto_atBot_cinfi

/- warning: tendsto_at_top_cinfi -> tendsto_atTop_cinfi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : InfConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) _inst_2] {f : ι -> α}, (Antitone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) f) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) (Set.range.{u1, succ u2} α ι f)) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atTop.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_3) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : InfConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) _inst_2] {f : ι -> α}, (Antitone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) f) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3)))) (Set.range.{u1, succ u2} α ι f)) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atTop.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_3) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align tendsto_at_top_cinfi tendsto_atTop_cinfiₓ'. -/
theorem tendsto_atTop_cinfi (h_anti : Antitone f) (hbdd : BddBelow <| range f) :
    Tendsto f atTop (𝓝 (⨅ i, f i)) := by convert tendsto_atBot_csupr h_anti.dual hbdd.dual
#align tendsto_at_top_cinfi tendsto_atTop_cinfi

end Cinfi

section supᵢ

variable [CompleteLattice α] [SupConvergenceClass α] {f : ι → α} {a : α}

/- warning: tendsto_at_top_supr -> tendsto_atTop_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : CompleteLattice.{u1} α] [_inst_4 : SupConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) _inst_2] {f : ι -> α}, (Monotone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) f) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atTop.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_3)) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : CompleteLattice.{u1} α] [_inst_4 : SupConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) _inst_2] {f : ι -> α}, (Monotone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) f) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atTop.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_3)) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align tendsto_at_top_supr tendsto_atTop_supᵢₓ'. -/
theorem tendsto_atTop_supᵢ (h_mono : Monotone f) : Tendsto f atTop (𝓝 (⨆ i, f i)) :=
  tendsto_atTop_csupr h_mono (OrderTop.bddAbove _)
#align tendsto_at_top_supr tendsto_atTop_supᵢ

/- warning: tendsto_at_bot_supr -> tendsto_atBot_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : CompleteLattice.{u1} α] [_inst_4 : SupConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) _inst_2] {f : ι -> α}, (Antitone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) f) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atBot.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_3)) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : CompleteLattice.{u1} α] [_inst_4 : SupConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) _inst_2] {f : ι -> α}, (Antitone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) f) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atBot.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_3)) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align tendsto_at_bot_supr tendsto_atBot_supᵢₓ'. -/
theorem tendsto_atBot_supᵢ (h_anti : Antitone f) : Tendsto f atBot (𝓝 (⨆ i, f i)) :=
  tendsto_atBot_csupr h_anti (OrderTop.bddAbove _)
#align tendsto_at_bot_supr tendsto_atBot_supᵢ

end supᵢ

section infᵢ

variable [CompleteLattice α] [InfConvergenceClass α] {f : ι → α} {a : α}

/- warning: tendsto_at_bot_infi -> tendsto_atBot_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : CompleteLattice.{u1} α] [_inst_4 : InfConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) _inst_2] {f : ι -> α}, (Monotone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) f) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atBot.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_3)) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : CompleteLattice.{u1} α] [_inst_4 : InfConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) _inst_2] {f : ι -> α}, (Monotone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) f) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atBot.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_3)) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align tendsto_at_bot_infi tendsto_atBot_infᵢₓ'. -/
theorem tendsto_atBot_infᵢ (h_mono : Monotone f) : Tendsto f atBot (𝓝 (⨅ i, f i)) :=
  tendsto_atBot_cinfi h_mono (OrderBot.bddBelow _)
#align tendsto_at_bot_infi tendsto_atBot_infᵢ

/- warning: tendsto_at_top_infi -> tendsto_atTop_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : CompleteLattice.{u1} α] [_inst_4 : InfConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) _inst_2] {f : ι -> α}, (Antitone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) f) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atTop.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_3)) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : CompleteLattice.{u1} α] [_inst_4 : InfConvergenceClass.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) _inst_2] {f : ι -> α}, (Antitone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_3))) f) -> (Filter.Tendsto.{u2, u1} ι α f (Filter.atTop.{u2} ι _inst_1) (nhds.{u1} α _inst_2 (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_3)) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align tendsto_at_top_infi tendsto_atTop_infᵢₓ'. -/
theorem tendsto_atTop_infᵢ (h_anti : Antitone f) : Tendsto f atTop (𝓝 (⨅ i, f i)) :=
  tendsto_atTop_cinfi h_anti (OrderBot.bddBelow _)
#align tendsto_at_top_infi tendsto_atTop_infᵢ

end infᵢ

end

instance [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β] [SupConvergenceClass α]
    [SupConvergenceClass β] : SupConvergenceClass (α × β) :=
  by
  constructor
  rintro ⟨a, b⟩ s h
  rw [isLUB_prod, ← range_restrict, ← range_restrict] at h
  have A : tendsto (fun x : s => (x : α × β).1) at_top (𝓝 a) :=
    tendsto_atTop_isLUB (monotone_fst.restrict s) h.1
  have B : tendsto (fun x : s => (x : α × β).2) at_top (𝓝 b) :=
    tendsto_atTop_isLUB (monotone_snd.restrict s) h.2
  convert A.prod_mk_nhds B
  ext1 ⟨⟨x, y⟩, h⟩
  rfl

instance [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β] [InfConvergenceClass α]
    [InfConvergenceClass β] : InfConvergenceClass (α × β) :=
  show InfConvergenceClass (αᵒᵈ × βᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

instance {ι : Type _} {α : ι → Type _} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, SupConvergenceClass (α i)] : SupConvergenceClass (∀ i, α i) :=
  by
  refine' ⟨fun f s h => _⟩
  simp only [isLUB_pi, ← range_restrict] at h
  exact tendsto_pi_nhds.2 fun i => tendsto_atTop_isLUB ((monotone_eval _).restrict _) (h i)

instance {ι : Type _} {α : ι → Type _} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, InfConvergenceClass (α i)] : InfConvergenceClass (∀ i, α i) :=
  show InfConvergenceClass (∀ i, (α i)ᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

#print Pi.Sup_convergence_class' /-
instance Pi.Sup_convergence_class' {ι : Type _} [Preorder α] [TopologicalSpace α]
    [SupConvergenceClass α] : SupConvergenceClass (ι → α) :=
  Pi.supConvergenceClass
#align pi.Sup_convergence_class' Pi.Sup_convergence_class'
-/

#print Pi.Inf_convergence_class' /-
instance Pi.Inf_convergence_class' {ι : Type _} [Preorder α] [TopologicalSpace α]
    [InfConvergenceClass α] : InfConvergenceClass (ι → α) :=
  Pi.infConvergenceClass
#align pi.Inf_convergence_class' Pi.Inf_convergence_class'
-/

/- warning: tendsto_of_monotone -> tendsto_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} ι] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : ConditionallyCompleteLinearOrder.{u2} α] [_inst_4 : OrderTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α _inst_3)))))] {f : ι -> α}, (Monotone.{u1, u2} ι α _inst_1 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α _inst_3))))) f) -> (Or (Filter.Tendsto.{u1, u2} ι α f (Filter.atTop.{u1} ι _inst_1) (Filter.atTop.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α _inst_3))))))) (Exists.{succ u2} α (fun (l : α) => Filter.Tendsto.{u1, u2} ι α f (Filter.atTop.{u1} ι _inst_1) (nhds.{u2} α _inst_2 l))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_4 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_3)))))] {f : ι -> α}, (Monotone.{u2, u1} ι α _inst_1 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_3))))) f) -> (Or (Filter.Tendsto.{u2, u1} ι α f (Filter.atTop.{u2} ι _inst_1) (Filter.atTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_3))))))) (Exists.{succ u1} α (fun (l : α) => Filter.Tendsto.{u2, u1} ι α f (Filter.atTop.{u2} ι _inst_1) (nhds.{u1} α _inst_2 l))))
Case conversion may be inaccurate. Consider using '#align tendsto_of_monotone tendsto_of_monotoneₓ'. -/
theorem tendsto_of_monotone {ι α : Type _} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Monotone f) :
    Tendsto f atTop atTop ∨ ∃ l, Tendsto f atTop (𝓝 l) :=
  if H : BddAbove (range f) then Or.inr ⟨_, tendsto_atTop_csupr h_mono H⟩
  else Or.inl <| tendsto_atTop_atTop_of_monotone' h_mono H
#align tendsto_of_monotone tendsto_of_monotone

/- warning: tendsto_iff_tendsto_subseq_of_monotone -> tendsto_iff_tendsto_subseq_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι₁ : Type.{u1}} {ι₂ : Type.{u2}} {α : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} ι₁] [_inst_2 : Preorder.{u2} ι₂] [_inst_3 : Nonempty.{succ u1} ι₁] [_inst_4 : TopologicalSpace.{u3} α] [_inst_5 : ConditionallyCompleteLinearOrder.{u3} α] [_inst_6 : OrderTopology.{u3} α _inst_4 (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} α _inst_5)))))] [_inst_7 : NoMaxOrder.{u3} α (Preorder.toLT.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} α _inst_5))))))] {f : ι₂ -> α} {φ : ι₁ -> ι₂} {l : α}, (Monotone.{u2, u3} ι₂ α _inst_2 (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} α _inst_5))))) f) -> (Filter.Tendsto.{u1, u2} ι₁ ι₂ φ (Filter.atTop.{u1} ι₁ (PartialOrder.toPreorder.{u1} ι₁ (SemilatticeSup.toPartialOrder.{u1} ι₁ _inst_1))) (Filter.atTop.{u2} ι₂ _inst_2)) -> (Iff (Filter.Tendsto.{u2, u3} ι₂ α f (Filter.atTop.{u2} ι₂ _inst_2) (nhds.{u3} α _inst_4 l)) (Filter.Tendsto.{u1, u3} ι₁ α (Function.comp.{succ u1, succ u2, succ u3} ι₁ ι₂ α f φ) (Filter.atTop.{u1} ι₁ (PartialOrder.toPreorder.{u1} ι₁ (SemilatticeSup.toPartialOrder.{u1} ι₁ _inst_1))) (nhds.{u3} α _inst_4 l)))
but is expected to have type
  forall {ι₁ : Type.{u3}} {ι₂ : Type.{u2}} {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u3} ι₁] [_inst_2 : Preorder.{u2} ι₂] [_inst_3 : Nonempty.{succ u3} ι₁] [_inst_4 : TopologicalSpace.{u1} α] [_inst_5 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_6 : OrderTopology.{u1} α _inst_4 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_5)))))] [_inst_7 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_5))))))] {f : ι₂ -> α} {φ : ι₁ -> ι₂} {l : α}, (Monotone.{u2, u1} ι₂ α _inst_2 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_5))))) f) -> (Filter.Tendsto.{u3, u2} ι₁ ι₂ φ (Filter.atTop.{u3} ι₁ (PartialOrder.toPreorder.{u3} ι₁ (SemilatticeSup.toPartialOrder.{u3} ι₁ _inst_1))) (Filter.atTop.{u2} ι₂ _inst_2)) -> (Iff (Filter.Tendsto.{u2, u1} ι₂ α f (Filter.atTop.{u2} ι₂ _inst_2) (nhds.{u1} α _inst_4 l)) (Filter.Tendsto.{u3, u1} ι₁ α (Function.comp.{succ u3, succ u2, succ u1} ι₁ ι₂ α f φ) (Filter.atTop.{u3} ι₁ (PartialOrder.toPreorder.{u3} ι₁ (SemilatticeSup.toPartialOrder.{u3} ι₁ _inst_1))) (nhds.{u1} α _inst_4 l)))
Case conversion may be inaccurate. Consider using '#align tendsto_iff_tendsto_subseq_of_monotone tendsto_iff_tendsto_subseq_of_monotoneₓ'. -/
theorem tendsto_iff_tendsto_subseq_of_monotone {ι₁ ι₂ α : Type _} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMaxOrder α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : Monotone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) :=
  by
  constructor <;> intro h
  · exact h.comp hg
  · rcases tendsto_of_monotone hf with (h' | ⟨l', hl'⟩)
    · exact (not_tendsto_atTop_of_tendsto_nhds h (h'.comp hg)).elim
    · rwa [tendsto_nhds_unique h (hl'.comp hg)]
#align tendsto_iff_tendsto_subseq_of_monotone tendsto_iff_tendsto_subseq_of_monotone

/-! The next family of results, such as `is_lub_of_tendsto_at_top` and `supr_eq_of_tendsto`, are
converses to the standard fact that bounded monotone functions converge. They state, that if a
monotone function `f` tends to `a` along `filter.at_top`, then that value `a` is a least upper bound
for the range of `f`.

Related theorems above (`is_lub.is_lub_of_tendsto`, `is_glb.is_glb_of_tendsto` etc) cover the case
when `f x` tends to `a` as `x` tends to some point `b` in the domain. -/


/- warning: monotone.ge_of_tendsto -> Monotone.ge_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_1 _inst_2] [_inst_4 : SemilatticeSup.{u2} β] {f : β -> α} {a : α}, (Monotone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_4)) _inst_2 f) -> (Filter.Tendsto.{u2, u1} β α f (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_4))) (nhds.{u1} α _inst_1 a)) -> (forall (b : β), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (f b) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_1 _inst_2] [_inst_4 : SemilatticeSup.{u1} β] {f : β -> α} {a : α}, (Monotone.{u1, u2} β α (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_4)) _inst_2 f) -> (Filter.Tendsto.{u1, u2} β α f (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_4))) (nhds.{u2} α _inst_1 a)) -> (forall (b : β), LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) (f b) a)
Case conversion may be inaccurate. Consider using '#align monotone.ge_of_tendsto Monotone.ge_of_tendstoₓ'. -/
theorem Monotone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f) (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    f b ≤ a :=
  haveI : Nonempty β := Nonempty.intro b
  ge_of_tendsto ha ((eventually_ge_at_top b).mono fun _ hxy => hf hxy)
#align monotone.ge_of_tendsto Monotone.ge_of_tendsto

/- warning: monotone.le_of_tendsto -> Monotone.le_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_1 _inst_2] [_inst_4 : SemilatticeInf.{u2} β] {f : β -> α} {a : α}, (Monotone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_4)) _inst_2 f) -> (Filter.Tendsto.{u2, u1} β α f (Filter.atBot.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_4))) (nhds.{u1} α _inst_1 a)) -> (forall (b : β), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_1 _inst_2] [_inst_4 : SemilatticeInf.{u1} β] {f : β -> α} {a : α}, (Monotone.{u1, u2} β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_4)) _inst_2 f) -> (Filter.Tendsto.{u1, u2} β α f (Filter.atBot.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_4))) (nhds.{u2} α _inst_1 a)) -> (forall (b : β), LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) a (f b))
Case conversion may be inaccurate. Consider using '#align monotone.le_of_tendsto Monotone.le_of_tendstoₓ'. -/
theorem Monotone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [SemilatticeInf β] {f : β → α} {a : α} (hf : Monotone f) (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual.ge_of_tendsto ha b
#align monotone.le_of_tendsto Monotone.le_of_tendsto

/- warning: antitone.le_of_tendsto -> Antitone.le_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_1 _inst_2] [_inst_4 : SemilatticeSup.{u2} β] {f : β -> α} {a : α}, (Antitone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_4)) _inst_2 f) -> (Filter.Tendsto.{u2, u1} β α f (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_4))) (nhds.{u1} α _inst_1 a)) -> (forall (b : β), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_1 _inst_2] [_inst_4 : SemilatticeSup.{u1} β] {f : β -> α} {a : α}, (Antitone.{u1, u2} β α (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_4)) _inst_2 f) -> (Filter.Tendsto.{u1, u2} β α f (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_4))) (nhds.{u2} α _inst_1 a)) -> (forall (b : β), LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) a (f b))
Case conversion may be inaccurate. Consider using '#align antitone.le_of_tendsto Antitone.le_of_tendstoₓ'. -/
theorem Antitone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [SemilatticeSup β] {f : β → α} {a : α} (hf : Antitone f) (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual_right.ge_of_tendsto ha b
#align antitone.le_of_tendsto Antitone.le_of_tendsto

/- warning: antitone.ge_of_tendsto -> Antitone.ge_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_1 _inst_2] [_inst_4 : SemilatticeInf.{u2} β] {f : β -> α} {a : α}, (Antitone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_4)) _inst_2 f) -> (Filter.Tendsto.{u2, u1} β α f (Filter.atBot.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_4))) (nhds.{u1} α _inst_1 a)) -> (forall (b : β), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (f b) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_1 _inst_2] [_inst_4 : SemilatticeInf.{u1} β] {f : β -> α} {a : α}, (Antitone.{u1, u2} β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_4)) _inst_2 f) -> (Filter.Tendsto.{u1, u2} β α f (Filter.atBot.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_4))) (nhds.{u2} α _inst_1 a)) -> (forall (b : β), LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) (f b) a)
Case conversion may be inaccurate. Consider using '#align antitone.ge_of_tendsto Antitone.ge_of_tendstoₓ'. -/
theorem Antitone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [SemilatticeInf β] {f : β → α} {a : α} (hf : Antitone f) (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    f b ≤ a :=
  hf.dual_right.le_of_tendsto ha b
#align antitone.ge_of_tendsto Antitone.ge_of_tendsto

/- warning: is_lub_of_tendsto_at_top -> isLUB_of_tendsto_atTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_1 _inst_2] [_inst_4 : Nonempty.{succ u2} β] [_inst_5 : SemilatticeSup.{u2} β] {f : β -> α} {a : α}, (Monotone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_5)) _inst_2 f) -> (Filter.Tendsto.{u2, u1} β α f (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_5))) (nhds.{u1} α _inst_1 a)) -> (IsLUB.{u1} α _inst_2 (Set.range.{u1, succ u2} α β f) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_1 _inst_2] [_inst_4 : Nonempty.{succ u1} β] [_inst_5 : SemilatticeSup.{u1} β] {f : β -> α} {a : α}, (Monotone.{u1, u2} β α (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5)) _inst_2 f) -> (Filter.Tendsto.{u1, u2} β α f (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5))) (nhds.{u2} α _inst_1 a)) -> (IsLUB.{u2} α _inst_2 (Set.range.{u2, succ u1} α β f) a)
Case conversion may be inaccurate. Consider using '#align is_lub_of_tendsto_at_top isLUB_of_tendsto_atTopₓ'. -/
theorem isLUB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsLUB (Set.range f) a :=
  by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.ge_of_tendsto ha b
  · exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)
#align is_lub_of_tendsto_at_top isLUB_of_tendsto_atTop

/- warning: is_glb_of_tendsto_at_bot -> isGLB_of_tendsto_atBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_1 _inst_2] [_inst_4 : Nonempty.{succ u2} β] [_inst_5 : SemilatticeInf.{u2} β] {f : β -> α} {a : α}, (Monotone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_5)) _inst_2 f) -> (Filter.Tendsto.{u2, u1} β α f (Filter.atBot.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_5))) (nhds.{u1} α _inst_1 a)) -> (IsGLB.{u1} α _inst_2 (Set.range.{u1, succ u2} α β f) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_1 _inst_2] [_inst_4 : Nonempty.{succ u1} β] [_inst_5 : SemilatticeInf.{u1} β] {f : β -> α} {a : α}, (Monotone.{u1, u2} β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_5)) _inst_2 f) -> (Filter.Tendsto.{u1, u2} β α f (Filter.atBot.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_5))) (nhds.{u2} α _inst_1 a)) -> (IsGLB.{u2} α _inst_2 (Set.range.{u2, succ u1} α β f) a)
Case conversion may be inaccurate. Consider using '#align is_glb_of_tendsto_at_bot isGLB_of_tendsto_atBotₓ'. -/
theorem isGLB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [SemilatticeInf β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsGLB (Set.range f) a :=
  @isLUB_of_tendsto_atTop αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ hf.dual ha
#align is_glb_of_tendsto_at_bot isGLB_of_tendsto_atBot

/- warning: is_lub_of_tendsto_at_bot -> isLUB_of_tendsto_atBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_1 _inst_2] [_inst_4 : Nonempty.{succ u2} β] [_inst_5 : SemilatticeInf.{u2} β] {f : β -> α} {a : α}, (Antitone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_5)) _inst_2 f) -> (Filter.Tendsto.{u2, u1} β α f (Filter.atBot.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_5))) (nhds.{u1} α _inst_1 a)) -> (IsLUB.{u1} α _inst_2 (Set.range.{u1, succ u2} α β f) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_1 _inst_2] [_inst_4 : Nonempty.{succ u1} β] [_inst_5 : SemilatticeInf.{u1} β] {f : β -> α} {a : α}, (Antitone.{u1, u2} β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_5)) _inst_2 f) -> (Filter.Tendsto.{u1, u2} β α f (Filter.atBot.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_5))) (nhds.{u2} α _inst_1 a)) -> (IsLUB.{u2} α _inst_2 (Set.range.{u2, succ u1} α β f) a)
Case conversion may be inaccurate. Consider using '#align is_lub_of_tendsto_at_bot isLUB_of_tendsto_atBotₓ'. -/
theorem isLUB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [SemilatticeInf β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsLUB (Set.range f) a :=
  @isLUB_of_tendsto_atTop α βᵒᵈ _ _ _ _ _ _ _ hf.dual_left ha
#align is_lub_of_tendsto_at_bot isLUB_of_tendsto_atBot

/- warning: is_glb_of_tendsto_at_top -> isGLB_of_tendsto_atTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_1 _inst_2] [_inst_4 : Nonempty.{succ u2} β] [_inst_5 : SemilatticeSup.{u2} β] {f : β -> α} {a : α}, (Antitone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_5)) _inst_2 f) -> (Filter.Tendsto.{u2, u1} β α f (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_5))) (nhds.{u1} α _inst_1 a)) -> (IsGLB.{u1} α _inst_2 (Set.range.{u1, succ u2} α β f) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_1 _inst_2] [_inst_4 : Nonempty.{succ u1} β] [_inst_5 : SemilatticeSup.{u1} β] {f : β -> α} {a : α}, (Antitone.{u1, u2} β α (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5)) _inst_2 f) -> (Filter.Tendsto.{u1, u2} β α f (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5))) (nhds.{u2} α _inst_1 a)) -> (IsGLB.{u2} α _inst_2 (Set.range.{u2, succ u1} α β f) a)
Case conversion may be inaccurate. Consider using '#align is_glb_of_tendsto_at_top isGLB_of_tendsto_atTopₓ'. -/
theorem isGLB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsGLB (Set.range f) a :=
  @isGLB_of_tendsto_atBot α βᵒᵈ _ _ _ _ _ _ _ hf.dual_left ha
#align is_glb_of_tendsto_at_top isGLB_of_tendsto_atTop

/- warning: supr_eq_of_tendsto -> supᵢ_eq_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : CompleteLinearOrder.{u1} α] [_inst_3 : OrderTopology.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_2))))] [_inst_4 : Nonempty.{succ u2} β] [_inst_5 : SemilatticeSup.{u2} β] {f : β -> α} {a : α}, (Monotone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_5)) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_2)))) f) -> (Filter.Tendsto.{u2, u1} β α f (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_5))) (nhds.{u1} α _inst_1 a)) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_2))) β f) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : CompleteLinearOrder.{u2} α] [_inst_3 : OrderTopology.{u2} α _inst_1 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_2))))] [_inst_4 : Nonempty.{succ u1} β] [_inst_5 : SemilatticeSup.{u1} β] {f : β -> α} {a : α}, (Monotone.{u1, u2} β α (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5)) (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_2)))) f) -> (Filter.Tendsto.{u1, u2} β α f (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5))) (nhds.{u2} α _inst_1 a)) -> (Eq.{succ u2} α (supᵢ.{u2, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} α _inst_2)))) β f) a)
Case conversion may be inaccurate. Consider using '#align supr_eq_of_tendsto supᵢ_eq_of_tendstoₓ'. -/
theorem supᵢ_eq_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f) :
    Tendsto f atTop (𝓝 a) → supᵢ f = a :=
  tendsto_nhds_unique (tendsto_atTop_supᵢ hf)
#align supr_eq_of_tendsto supᵢ_eq_of_tendsto

/- warning: infi_eq_of_tendsto -> infᵢ_eq_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : CompleteLinearOrder.{u2} α] [_inst_3 : OrderTopology.{u2} α _inst_1 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_2))))] [_inst_4 : Nonempty.{succ u1} β] [_inst_5 : SemilatticeSup.{u1} β] {f : β -> α} {a : α}, (Antitone.{u1, u2} β α (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5)) (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_2)))) f) -> (Filter.Tendsto.{u1, u2} β α f (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5))) (nhds.{u2} α _inst_1 a)) -> (Eq.{succ u2} α (infᵢ.{u2, succ u1} α (ConditionallyCompleteLattice.toHasInf.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_2))) β f) a)
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : CompleteLinearOrder.{u2} α] [_inst_3 : OrderTopology.{u2} α _inst_1 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_2))))] [_inst_4 : Nonempty.{succ u1} β] [_inst_5 : SemilatticeSup.{u1} β] {f : β -> α} {a : α}, (Antitone.{u1, u2} β α (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5)) (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_2)))) f) -> (Filter.Tendsto.{u1, u2} β α f (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5))) (nhds.{u2} α _inst_1 a)) -> (Eq.{succ u2} α (infᵢ.{u2, succ u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} α _inst_2)))) β f) a)
Case conversion may be inaccurate. Consider using '#align infi_eq_of_tendsto infᵢ_eq_of_tendstoₓ'. -/
theorem infᵢ_eq_of_tendsto {α} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Antitone f) :
    Tendsto f atTop (𝓝 a) → infᵢ f = a :=
  tendsto_nhds_unique (tendsto_atTop_infᵢ hf)
#align infi_eq_of_tendsto infᵢ_eq_of_tendsto

/- warning: supr_eq_supr_subseq_of_monotone -> supᵢ_eq_supᵢ_subseq_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι₁ : Type.{u1}} {ι₂ : Type.{u2}} {α : Type.{u3}} [_inst_1 : Preorder.{u2} ι₂] [_inst_2 : CompleteLattice.{u3} α] {l : Filter.{u1} ι₁} [_inst_3 : Filter.NeBot.{u1} ι₁ l] {f : ι₂ -> α} {φ : ι₁ -> ι₂}, (Monotone.{u2, u3} ι₂ α _inst_1 (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_2))) f) -> (Filter.Tendsto.{u1, u2} ι₁ ι₂ φ l (Filter.atTop.{u2} ι₂ _inst_1)) -> (Eq.{succ u3} α (supᵢ.{u3, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u3} α (CompleteLattice.toConditionallyCompleteLattice.{u3} α _inst_2)) ι₂ (fun (i : ι₂) => f i)) (supᵢ.{u3, succ u1} α (ConditionallyCompleteLattice.toHasSup.{u3} α (CompleteLattice.toConditionallyCompleteLattice.{u3} α _inst_2)) ι₁ (fun (i : ι₁) => f (φ i))))
but is expected to have type
  forall {ι₁ : Type.{u3}} {ι₂ : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} ι₂] [_inst_2 : CompleteLattice.{u1} α] {l : Filter.{u3} ι₁} [_inst_3 : Filter.NeBot.{u3} ι₁ l] {f : ι₂ -> α} {φ : ι₁ -> ι₂}, (Monotone.{u2, u1} ι₂ α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2))) f) -> (Filter.Tendsto.{u3, u2} ι₁ ι₂ φ l (Filter.atTop.{u2} ι₂ _inst_1)) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2)) ι₂ (fun (i : ι₂) => f i)) (supᵢ.{u1, succ u3} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2)) ι₁ (fun (i : ι₁) => f (φ i))))
Case conversion may be inaccurate. Consider using '#align supr_eq_supr_subseq_of_monotone supᵢ_eq_supᵢ_subseq_of_monotoneₓ'. -/
theorem supᵢ_eq_supᵢ_subseq_of_monotone {ι₁ ι₂ α : Type _} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.ne_bot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atTop) : (⨆ i, f i) = ⨆ i, f (φ i) :=
  le_antisymm
    (supᵢ_mono' fun i =>
      Exists.imp (fun j (hj : i ≤ φ j) => hf hj) (hφ.Eventually <| eventually_ge_atTop i).exists)
    (supᵢ_mono' fun i => ⟨φ i, le_rfl⟩)
#align supr_eq_supr_subseq_of_monotone supᵢ_eq_supᵢ_subseq_of_monotone

/- warning: infi_eq_infi_subseq_of_monotone -> infᵢ_eq_infᵢ_subseq_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι₁ : Type.{u1}} {ι₂ : Type.{u2}} {α : Type.{u3}} [_inst_1 : Preorder.{u2} ι₂] [_inst_2 : CompleteLattice.{u3} α] {l : Filter.{u1} ι₁} [_inst_3 : Filter.NeBot.{u1} ι₁ l] {f : ι₂ -> α} {φ : ι₁ -> ι₂}, (Monotone.{u2, u3} ι₂ α _inst_1 (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_2))) f) -> (Filter.Tendsto.{u1, u2} ι₁ ι₂ φ l (Filter.atBot.{u2} ι₂ _inst_1)) -> (Eq.{succ u3} α (infᵢ.{u3, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u3} α (CompleteLattice.toConditionallyCompleteLattice.{u3} α _inst_2)) ι₂ (fun (i : ι₂) => f i)) (infᵢ.{u3, succ u1} α (ConditionallyCompleteLattice.toHasInf.{u3} α (CompleteLattice.toConditionallyCompleteLattice.{u3} α _inst_2)) ι₁ (fun (i : ι₁) => f (φ i))))
but is expected to have type
  forall {ι₁ : Type.{u3}} {ι₂ : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} ι₂] [_inst_2 : CompleteLattice.{u1} α] {l : Filter.{u3} ι₁} [_inst_3 : Filter.NeBot.{u3} ι₁ l] {f : ι₂ -> α} {φ : ι₁ -> ι₂}, (Monotone.{u2, u1} ι₂ α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2))) f) -> (Filter.Tendsto.{u3, u2} ι₁ ι₂ φ l (Filter.atBot.{u2} ι₂ _inst_1)) -> (Eq.{succ u1} α (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2)) ι₂ (fun (i : ι₂) => f i)) (infᵢ.{u1, succ u3} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2)) ι₁ (fun (i : ι₁) => f (φ i))))
Case conversion may be inaccurate. Consider using '#align infi_eq_infi_subseq_of_monotone infᵢ_eq_infᵢ_subseq_of_monotoneₓ'. -/
theorem infᵢ_eq_infᵢ_subseq_of_monotone {ι₁ ι₂ α : Type _} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.ne_bot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atBot) : (⨅ i, f i) = ⨅ i, f (φ i) :=
  supᵢ_eq_supᵢ_subseq_of_monotone hf.dual hφ
#align infi_eq_infi_subseq_of_monotone infᵢ_eq_infᵢ_subseq_of_monotone

