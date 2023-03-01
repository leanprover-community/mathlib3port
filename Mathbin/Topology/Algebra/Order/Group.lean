/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.group
! leanprover-community/mathlib commit 3dadefa3f544b1db6214777fe47910739b54c66a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order.Basic
import Mathbin.Topology.Algebra.Group.Basic

/-!
# Topology on a linear ordered additive commutative group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that a linear ordered additive commutative group with order topology is a
topological group. We also prove continuity of `abs : G → G` and provide convenience lemmas like
`continuous_at.abs`.
-/


open Set Filter

open Topology Filter

variable {α G : Type _} [TopologicalSpace G] [LinearOrderedAddCommGroup G] [OrderTopology G]

variable {l : Filter α} {f g : α → G}

#print LinearOrderedAddCommGroup.topologicalAddGroup /-
-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedAddCommGroup.topologicalAddGroup : TopologicalAddGroup G
    where
  continuous_add := by
    refine' continuous_iff_continuousAt.2 _
    rintro ⟨a, b⟩
    refine' LinearOrderedAddCommGroup.tendsto_nhds.2 fun ε ε0 => _
    rcases dense_or_discrete 0 ε with (⟨δ, δ0, δε⟩ | ⟨h₁, h₂⟩)
    · -- If there exists `δ ∈ (0, ε)`, then we choose `δ`-nhd of `a` and `(ε-δ)`-nhd of `b`
      filter_upwards [(eventually_abs_sub_lt a δ0).prod_nhds
          (eventually_abs_sub_lt b (sub_pos.2 δε))]
      rintro ⟨x, y⟩ ⟨hx : |x - a| < δ, hy : |y - b| < ε - δ⟩
      rw [add_sub_add_comm]
      calc
        |x - a + (y - b)| ≤ |x - a| + |y - b| := abs_add _ _
        _ < δ + (ε - δ) := (add_lt_add hx hy)
        _ = ε := add_sub_cancel'_right _ _
        
    · -- Otherwise `ε`-nhd of each point `a` is `{a}`
      have hε : ∀ {x y}, |x - y| < ε → x = y :=
        by
        intro x y h
        simpa [sub_eq_zero] using h₂ _ h
      filter_upwards [(eventually_abs_sub_lt a ε0).prod_nhds (eventually_abs_sub_lt b ε0)]
      rintro ⟨x, y⟩ ⟨hx : |x - a| < ε, hy : |y - b| < ε⟩
      simpa [hε hx, hε hy]
  continuous_neg :=
    continuous_iff_continuousAt.2 fun a =>
      LinearOrderedAddCommGroup.tendsto_nhds.2 fun ε ε0 =>
        (eventually_abs_sub_lt a ε0).mono fun x hx => by rwa [neg_sub_neg, abs_sub_comm]
#align linear_ordered_add_comm_group.topological_add_group LinearOrderedAddCommGroup.topologicalAddGroup
-/

/- warning: continuous_abs -> continuous_abs is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : LinearOrderedAddCommGroup.{u1} G] [_inst_3 : OrderTopology.{u1} G _inst_1 (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))], Continuous.{u1, u1} G G _inst_1 _inst_1 (Abs.abs.{u1} G (Neg.toHasAbs.{u1} G (SubNegMonoid.toHasNeg.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))) (SemilatticeSup.toHasSup.{u1} G (Lattice.toSemilatticeSup.{u1} G (LinearOrder.toLattice.{u1} G (LinearOrderedAddCommGroup.toLinearOrder.{u1} G _inst_2))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : LinearOrderedAddCommGroup.{u1} G] [_inst_3 : OrderTopology.{u1} G _inst_1 (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))], Continuous.{u1, u1} G G _inst_1 _inst_1 (Abs.abs.{u1} G (Neg.toHasAbs.{u1} G (NegZeroClass.toNeg.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))) (SemilatticeSup.toSup.{u1} G (Lattice.toSemilatticeSup.{u1} G (DistribLattice.toLattice.{u1} G (instDistribLattice.{u1} G (LinearOrderedAddCommGroup.toLinearOrder.{u1} G _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align continuous_abs continuous_absₓ'. -/
@[continuity]
theorem continuous_abs : Continuous (abs : G → G) :=
  continuous_id.max continuous_neg
#align continuous_abs continuous_abs

/- warning: filter.tendsto.abs -> Filter.Tendsto.abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : LinearOrderedAddCommGroup.{u2} G] [_inst_3 : OrderTopology.{u2} G _inst_1 (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2)))] {l : Filter.{u1} α} {f : α -> G} {a : G}, (Filter.Tendsto.{u1, u2} α G f l (nhds.{u2} G _inst_1 a)) -> (Filter.Tendsto.{u1, u2} α G (fun (x : α) => Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (SubNegMonoid.toHasNeg.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2))))) (SemilatticeSup.toHasSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (LinearOrder.toLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_2))))) (f x)) l (nhds.{u2} G _inst_1 (Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (SubNegMonoid.toHasNeg.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2))))) (SemilatticeSup.toHasSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (LinearOrder.toLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_2))))) a)))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : LinearOrderedAddCommGroup.{u1} G] [_inst_3 : OrderTopology.{u1} G _inst_1 (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))] {l : Filter.{u2} α} {f : α -> G} {a : G}, (Filter.Tendsto.{u2, u1} α G f l (nhds.{u1} G _inst_1 a)) -> (Filter.Tendsto.{u2, u1} α G (fun (x : α) => Abs.abs.{u1} G (Neg.toHasAbs.{u1} G (NegZeroClass.toNeg.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))) (SemilatticeSup.toSup.{u1} G (Lattice.toSemilatticeSup.{u1} G (DistribLattice.toLattice.{u1} G (instDistribLattice.{u1} G (LinearOrderedAddCommGroup.toLinearOrder.{u1} G _inst_2)))))) (f x)) l (nhds.{u1} G _inst_1 (Abs.abs.{u1} G (Neg.toHasAbs.{u1} G (NegZeroClass.toNeg.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))) (SemilatticeSup.toSup.{u1} G (Lattice.toSemilatticeSup.{u1} G (DistribLattice.toLattice.{u1} G (instDistribLattice.{u1} G (LinearOrderedAddCommGroup.toLinearOrder.{u1} G _inst_2)))))) a)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.abs Filter.Tendsto.absₓ'. -/
protected theorem Filter.Tendsto.abs {a : G} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun x => |f x|) l (𝓝 (|a|)) :=
  (continuous_abs.Tendsto _).comp h
#align filter.tendsto.abs Filter.Tendsto.abs

/- warning: tendsto_zero_iff_abs_tendsto_zero -> tendsto_zero_iff_abs_tendsto_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : LinearOrderedAddCommGroup.{u2} G] [_inst_3 : OrderTopology.{u2} G _inst_1 (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2)))] {l : Filter.{u1} α} (f : α -> G), Iff (Filter.Tendsto.{u1, u2} α G f l (nhds.{u2} G _inst_1 (OfNat.ofNat.{u2} G 0 (OfNat.mk.{u2} G 0 (Zero.zero.{u2} G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2)))))))))))) (Filter.Tendsto.{u1, u2} α G (Function.comp.{succ u1, succ u2, succ u2} α G G (Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (SubNegMonoid.toHasNeg.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2))))) (SemilatticeSup.toHasSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (LinearOrder.toLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_2)))))) f) l (nhds.{u2} G _inst_1 (OfNat.ofNat.{u2} G 0 (OfNat.mk.{u2} G 0 (Zero.zero.{u2} G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2))))))))))))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : LinearOrderedAddCommGroup.{u1} G] [_inst_3 : OrderTopology.{u1} G _inst_1 (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))] {l : Filter.{u2} α} (f : α -> G), Iff (Filter.Tendsto.{u2, u1} α G f l (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))))))) (Filter.Tendsto.{u2, u1} α G (Function.comp.{succ u2, succ u1, succ u1} α G G (Abs.abs.{u1} G (Neg.toHasAbs.{u1} G (NegZeroClass.toNeg.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))) (SemilatticeSup.toSup.{u1} G (Lattice.toSemilatticeSup.{u1} G (DistribLattice.toLattice.{u1} G (instDistribLattice.{u1} G (LinearOrderedAddCommGroup.toLinearOrder.{u1} G _inst_2))))))) f) l (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))))))))))
Case conversion may be inaccurate. Consider using '#align tendsto_zero_iff_abs_tendsto_zero tendsto_zero_iff_abs_tendsto_zeroₓ'. -/
theorem tendsto_zero_iff_abs_tendsto_zero (f : α → G) :
    Tendsto f l (𝓝 0) ↔ Tendsto (abs ∘ f) l (𝓝 0) :=
  by
  refine' ⟨fun h => (abs_zero : |(0 : G)| = 0) ▸ h.abs, fun h => _⟩
  have : tendsto (fun a => -|f a|) l (𝓝 0) := (neg_zero : -(0 : G) = 0) ▸ h.neg
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le this h (fun x => neg_abs_le_self <| f x) fun x =>
      le_abs_self <| f x
#align tendsto_zero_iff_abs_tendsto_zero tendsto_zero_iff_abs_tendsto_zero

variable [TopologicalSpace α] {a : α} {s : Set α}

/- warning: continuous.abs -> Continuous.abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : LinearOrderedAddCommGroup.{u2} G] [_inst_3 : OrderTopology.{u2} G _inst_1 (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2)))] {f : α -> G} [_inst_4 : TopologicalSpace.{u1} α], (Continuous.{u1, u2} α G _inst_4 _inst_1 f) -> (Continuous.{u1, u2} α G _inst_4 _inst_1 (fun (x : α) => Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (SubNegMonoid.toHasNeg.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2))))) (SemilatticeSup.toHasSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (LinearOrder.toLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_2))))) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : LinearOrderedAddCommGroup.{u1} G] [_inst_3 : OrderTopology.{u1} G _inst_1 (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))] {f : α -> G} [_inst_4 : TopologicalSpace.{u2} α], (Continuous.{u2, u1} α G _inst_4 _inst_1 f) -> (Continuous.{u2, u1} α G _inst_4 _inst_1 (fun (x : α) => Abs.abs.{u1} G (Neg.toHasAbs.{u1} G (NegZeroClass.toNeg.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))) (SemilatticeSup.toSup.{u1} G (Lattice.toSemilatticeSup.{u1} G (DistribLattice.toLattice.{u1} G (instDistribLattice.{u1} G (LinearOrderedAddCommGroup.toLinearOrder.{u1} G _inst_2)))))) (f x)))
Case conversion may be inaccurate. Consider using '#align continuous.abs Continuous.absₓ'. -/
protected theorem Continuous.abs (h : Continuous f) : Continuous fun x => |f x| :=
  continuous_abs.comp h
#align continuous.abs Continuous.abs

/- warning: continuous_at.abs -> ContinuousAt.abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : LinearOrderedAddCommGroup.{u2} G] [_inst_3 : OrderTopology.{u2} G _inst_1 (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2)))] {f : α -> G} [_inst_4 : TopologicalSpace.{u1} α] {a : α}, (ContinuousAt.{u1, u2} α G _inst_4 _inst_1 f a) -> (ContinuousAt.{u1, u2} α G _inst_4 _inst_1 (fun (x : α) => Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (SubNegMonoid.toHasNeg.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2))))) (SemilatticeSup.toHasSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (LinearOrder.toLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_2))))) (f x)) a)
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : LinearOrderedAddCommGroup.{u1} G] [_inst_3 : OrderTopology.{u1} G _inst_1 (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))] {f : α -> G} [_inst_4 : TopologicalSpace.{u2} α] {a : α}, (ContinuousAt.{u2, u1} α G _inst_4 _inst_1 f a) -> (ContinuousAt.{u2, u1} α G _inst_4 _inst_1 (fun (x : α) => Abs.abs.{u1} G (Neg.toHasAbs.{u1} G (NegZeroClass.toNeg.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))) (SemilatticeSup.toSup.{u1} G (Lattice.toSemilatticeSup.{u1} G (DistribLattice.toLattice.{u1} G (instDistribLattice.{u1} G (LinearOrderedAddCommGroup.toLinearOrder.{u1} G _inst_2)))))) (f x)) a)
Case conversion may be inaccurate. Consider using '#align continuous_at.abs ContinuousAt.absₓ'. -/
protected theorem ContinuousAt.abs (h : ContinuousAt f a) : ContinuousAt (fun x => |f x|) a :=
  h.abs
#align continuous_at.abs ContinuousAt.abs

/- warning: continuous_within_at.abs -> ContinuousWithinAt.abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : LinearOrderedAddCommGroup.{u2} G] [_inst_3 : OrderTopology.{u2} G _inst_1 (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2)))] {f : α -> G} [_inst_4 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α}, (ContinuousWithinAt.{u1, u2} α G _inst_4 _inst_1 f s a) -> (ContinuousWithinAt.{u1, u2} α G _inst_4 _inst_1 (fun (x : α) => Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (SubNegMonoid.toHasNeg.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2))))) (SemilatticeSup.toHasSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (LinearOrder.toLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_2))))) (f x)) s a)
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : LinearOrderedAddCommGroup.{u1} G] [_inst_3 : OrderTopology.{u1} G _inst_1 (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))] {f : α -> G} [_inst_4 : TopologicalSpace.{u2} α] {a : α} {s : Set.{u2} α}, (ContinuousWithinAt.{u2, u1} α G _inst_4 _inst_1 f s a) -> (ContinuousWithinAt.{u2, u1} α G _inst_4 _inst_1 (fun (x : α) => Abs.abs.{u1} G (Neg.toHasAbs.{u1} G (NegZeroClass.toNeg.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))) (SemilatticeSup.toSup.{u1} G (Lattice.toSemilatticeSup.{u1} G (DistribLattice.toLattice.{u1} G (instDistribLattice.{u1} G (LinearOrderedAddCommGroup.toLinearOrder.{u1} G _inst_2)))))) (f x)) s a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.abs ContinuousWithinAt.absₓ'. -/
protected theorem ContinuousWithinAt.abs (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => |f x|) s a :=
  h.abs
#align continuous_within_at.abs ContinuousWithinAt.abs

/- warning: continuous_on.abs -> ContinuousOn.abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : LinearOrderedAddCommGroup.{u2} G] [_inst_3 : OrderTopology.{u2} G _inst_1 (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2)))] {f : α -> G} [_inst_4 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (ContinuousOn.{u1, u2} α G _inst_4 _inst_1 f s) -> (ContinuousOn.{u1, u2} α G _inst_4 _inst_1 (fun (x : α) => Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (SubNegMonoid.toHasNeg.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_2))))) (SemilatticeSup.toHasSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (LinearOrder.toLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_2))))) (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : LinearOrderedAddCommGroup.{u1} G] [_inst_3 : OrderTopology.{u1} G _inst_1 (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))] {f : α -> G} [_inst_4 : TopologicalSpace.{u2} α] {s : Set.{u2} α}, (ContinuousOn.{u2, u1} α G _inst_4 _inst_1 f s) -> (ContinuousOn.{u2, u1} α G _inst_4 _inst_1 (fun (x : α) => Abs.abs.{u1} G (Neg.toHasAbs.{u1} G (NegZeroClass.toNeg.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))) (SemilatticeSup.toSup.{u1} G (Lattice.toSemilatticeSup.{u1} G (DistribLattice.toLattice.{u1} G (instDistribLattice.{u1} G (LinearOrderedAddCommGroup.toLinearOrder.{u1} G _inst_2)))))) (f x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.abs ContinuousOn.absₓ'. -/
protected theorem ContinuousOn.abs (h : ContinuousOn f s) : ContinuousOn (fun x => |f x|) s :=
  fun x hx => (h x hx).abs
#align continuous_on.abs ContinuousOn.abs

/- warning: tendsto_abs_nhds_within_zero -> tendsto_abs_nhdsWithin_zero is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : LinearOrderedAddCommGroup.{u1} G] [_inst_3 : OrderTopology.{u1} G _inst_1 (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))], Filter.Tendsto.{u1, u1} G G (Abs.abs.{u1} G (Neg.toHasAbs.{u1} G (SubNegMonoid.toHasNeg.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))) (SemilatticeSup.toHasSup.{u1} G (Lattice.toSemilatticeSup.{u1} G (LinearOrder.toLattice.{u1} G (LinearOrderedAddCommGroup.toLinearOrder.{u1} G _inst_2)))))) (nhdsWithin.{u1} G _inst_1 (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))))))))) (HasCompl.compl.{u1} (Set.{u1} G) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} G) (Set.booleanAlgebra.{u1} G)) (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.hasSingleton.{u1} G) (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))))))))) (nhdsWithin.{u1} G _inst_1 (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))))))))) (Set.Ioi.{u1} G (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))) (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : LinearOrderedAddCommGroup.{u1} G] [_inst_3 : OrderTopology.{u1} G _inst_1 (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))], Filter.Tendsto.{u1, u1} G G (Abs.abs.{u1} G (Neg.toHasAbs.{u1} G (NegZeroClass.toNeg.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))) (SemilatticeSup.toSup.{u1} G (Lattice.toSemilatticeSup.{u1} G (DistribLattice.toLattice.{u1} G (instDistribLattice.{u1} G (LinearOrderedAddCommGroup.toLinearOrder.{u1} G _inst_2))))))) (nhdsWithin.{u1} G _inst_1 (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))))) (HasCompl.compl.{u1} (Set.{u1} G) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} G) (Set.instBooleanAlgebraSet.{u1} G)) (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.instSingletonSet.{u1} G) (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))))))))))) (nhdsWithin.{u1} G _inst_1 (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))))))))) (Set.Ioi.{u1} G (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2))) (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_2)))))))))))
Case conversion may be inaccurate. Consider using '#align tendsto_abs_nhds_within_zero tendsto_abs_nhdsWithin_zeroₓ'. -/
theorem tendsto_abs_nhdsWithin_zero : Tendsto (abs : G → G) (𝓝[≠] 0) (𝓝[>] 0) :=
  (continuous_abs.tendsto' (0 : G) 0 abs_zero).inf <|
    tendsto_principal_principal.2 fun x => abs_pos.2
#align tendsto_abs_nhds_within_zero tendsto_abs_nhdsWithin_zero

