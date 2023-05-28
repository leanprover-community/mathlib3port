/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.urysohns_bounded
! leanprover-community/mathlib commit 38df578a6450a8c5142b3727e3ae894c2300cae0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UrysohnsLemma
import Mathbin.Topology.ContinuousFunction.Bounded

/-!
# Urysohn's lemma for bounded continuous functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we reformulate Urysohn's lemma `exists_continuous_zero_one_of_closed` in terms of
bounded continuous functions `X →ᵇ ℝ`. These lemmas live in a separate file because
`topology.continuous_function.bounded` imports too many other files.

## Tags

Urysohn's lemma, normal topological space
-/


open BoundedContinuousFunction

open Set Function

/- warning: exists_bounded_zero_one_of_closed -> exists_bounded_zero_one_of_closed is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : NormalSpace.{u1} X _inst_1] {s : Set.{u1} X} {t : Set.{u1} X}, (IsClosed.{u1} X _inst_1 s) -> (IsClosed.{u1} X _inst_1 t) -> (Disjoint.{u1} (Set.{u1} X) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} X) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} X) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} X) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} X) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} X) (Set.completeBooleanAlgebra.{u1} X)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} X) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X))) s t) -> (Exists.{succ u1} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) (fun (f : BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) => And (Set.EqOn.{u1, 0} X Real (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) => X -> Real) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) f) (OfNat.ofNat.{u1} (X -> Real) 0 (OfNat.mk.{u1} (X -> Real) 0 (Zero.zero.{u1} (X -> Real) (Pi.instZero.{u1, 0} X (fun (ᾰ : X) => Real) (fun (i : X) => Real.hasZero))))) s) (And (Set.EqOn.{u1, 0} X Real (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) => X -> Real) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) f) (OfNat.ofNat.{u1} (X -> Real) 1 (OfNat.mk.{u1} (X -> Real) 1 (One.one.{u1} (X -> Real) (Pi.instOne.{u1, 0} X (fun (ᾰ : X) => Real) (fun (i : X) => Real.hasOne))))) t) (forall (x : X), Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) => X -> Real) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) f x) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : NormalSpace.{u1} X _inst_1] {s : Set.{u1} X} {t : Set.{u1} X}, (IsClosed.{u1} X _inst_1 s) -> (IsClosed.{u1} X _inst_1 t) -> (Disjoint.{u1} (Set.{u1} X) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} X) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} X) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} X) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} X) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} X) (Set.instCompleteBooleanAlgebraSet.{u1} X)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} X) (Preorder.toLE.{u1} (Set.{u1} X) (PartialOrder.toPreorder.{u1} (Set.{u1} X) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} X) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} X) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} X) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} X) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} X) (Set.instCompleteBooleanAlgebraSet.{u1} X)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} X) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} X) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} X) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} X) (Set.instCompleteBooleanAlgebraSet.{u1} X)))))) s t) -> (Exists.{succ u1} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) (fun (f : BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) => And (Set.EqOn.{u1, 0} X Real (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) X (fun (_x : X) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : X) => Real) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) X Real _inst_1 Real.pseudoMetricSpace (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace))) f) (OfNat.ofNat.{u1} (X -> Real) 0 (Zero.toOfNat0.{u1} (X -> Real) (Pi.instZero.{u1, 0} X (fun (a._@.Mathlib.Data.Set.Function._hyg.1349 : X) => Real) (fun (i : X) => Real.instZeroReal)))) s) (And (Set.EqOn.{u1, 0} X Real (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) X (fun (_x : X) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : X) => Real) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) X Real _inst_1 Real.pseudoMetricSpace (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace))) f) (OfNat.ofNat.{u1} (X -> Real) 1 (One.toOfNat1.{u1} (X -> Real) (Pi.instOne.{u1, 0} X (fun (a._@.Mathlib.Data.Set.Function._hyg.1349 : X) => Real) (fun (i : X) => Real.instOneReal)))) t) (forall (x : X), Membership.mem.{0, 0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : X) => Real) x) (Set.{0} Real) (Set.instMembershipSet.{0} Real) (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) X (fun (_x : X) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : X) => Real) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace) X Real _inst_1 Real.pseudoMetricSpace (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} X Real _inst_1 Real.pseudoMetricSpace))) f x) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))))))
Case conversion may be inaccurate. Consider using '#align exists_bounded_zero_one_of_closed exists_bounded_zero_one_of_closedₓ'. -/
/-- Urysohns lemma: if `s` and `t` are two disjoint closed sets in a normal topological space `X`,
then there exists a continuous function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
theorem exists_bounded_zero_one_of_closed {X : Type _} [TopologicalSpace X] [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : X →ᵇ ℝ, EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  let ⟨f, hfs, hft, hf⟩ := exists_continuous_zero_one_of_closed hs ht hd
  ⟨⟨f, 1, fun x y => Real.dist_le_of_mem_Icc_01 (hf _) (hf _)⟩, hfs, hft, hf⟩
#align exists_bounded_zero_one_of_closed exists_bounded_zero_one_of_closed

/- warning: exists_bounded_mem_Icc_of_closed_of_le -> exists_bounded_mem_Icc_of_closed_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align exists_bounded_mem_Icc_of_closed_of_le exists_bounded_mem_Icc_of_closed_of_leₓ'. -/
/-- Urysohns lemma: if `s` and `t` are two disjoint closed sets in a normal topological space `X`,
and `a ≤ b` are two real numbers, then there exists a continuous function `f : X → ℝ` such that

* `f` equals `a` on `s`;
* `f` equals `b` on `t`;
* `a ≤ f x ≤ b` for all `x`.
-/
theorem exists_bounded_mem_Icc_of_closed_of_le {X : Type _} [TopologicalSpace X] [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) {a b : ℝ} (hle : a ≤ b) :
    ∃ f : X →ᵇ ℝ, EqOn f (const X a) s ∧ EqOn f (const X b) t ∧ ∀ x, f x ∈ Icc a b :=
  let ⟨f, hfs, hft, hf01⟩ := exists_bounded_zero_one_of_closed hs ht hd
  ⟨BoundedContinuousFunction.const X a + (b - a) • f, fun x hx => by simp [hfs hx], fun x hx => by
    simp [hft hx], fun x =>
    ⟨by dsimp <;> nlinarith [(hf01 x).1], by dsimp <;> nlinarith [(hf01 x).2]⟩⟩
#align exists_bounded_mem_Icc_of_closed_of_le exists_bounded_mem_Icc_of_closed_of_le

