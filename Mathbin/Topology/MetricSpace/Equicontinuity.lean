/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.metric_space.equicontinuity
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.Basic
import Mathbin.Topology.UniformSpace.Equicontinuity

/-!
# Equicontinuity in metric spaces

This files contains various facts about (uniform) equicontinuity in metric spaces. Most
importantly, we prove the usual characterization of equicontinuity of `F` at `x₀` in the case of
(pseudo) metric spaces: `∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ i, dist (F i x₀) (F i x) < ε`,
and we prove that functions sharing a common (local or global) continuity modulus are
(locally or uniformly) equicontinuous.

## Main statements

* `equicontinuous_at_iff`: characterization of equicontinuity for families of functions between
  (pseudo) metric spaces.
* `equicontinuous_at_of_continuity_modulus`: convenient way to prove equicontinuity at a point of
  a family of functions to a (pseudo) metric space by showing that they share a common *local*
  continuity modulus.
* `uniform_equicontinuous_of_continuity_modulus`: convenient way to prove uniform equicontinuity
  of a family of functions to a (pseudo) metric space by showing that they share a common *global*
  continuity modulus.

## Tags

equicontinuity, continuity modulus
-/


open Filter

open Topology uniformity

variable {α β ι : Type _} [PseudoMetricSpace α]

namespace Metric

/- warning: metric.equicontinuous_at_iff_right -> Metric.equicontinuousAt_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {F : ι -> β -> α} {x₀ : β}, Iff (EquicontinuousAt.{u3, u2, u1} ι β α _inst_2 (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F x₀) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Eventually.{u2} β (fun (x : β) => forall (i : ι), LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (F i x₀) (F i x)) ε) (nhds.{u2} β _inst_2 x₀)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {F : ι -> β -> α} {x₀ : β}, Iff (EquicontinuousAt.{u3, u2, u1} ι β α _inst_2 (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F x₀) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Eventually.{u2} β (fun (x : β) => forall (i : ι), LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (F i x₀) (F i x)) ε) (nhds.{u2} β _inst_2 x₀)))
Case conversion may be inaccurate. Consider using '#align metric.equicontinuous_at_iff_right Metric.equicontinuousAt_iff_rightₓ'. -/
/-- Characterization of equicontinuity for families of functions taking values in a (pseudo) metric
space. -/
theorem equicontinuousAt_iff_right {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {x₀ : β} :
    EquicontinuousAt F x₀ ↔ ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ∀ i, dist (F i x₀) (F i x) < ε :=
  uniformity_basis_dist.equicontinuousAt_iff_right
#align metric.equicontinuous_at_iff_right Metric.equicontinuousAt_iff_right

/- warning: metric.equicontinuous_at_iff -> Metric.equicontinuousAt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : PseudoMetricSpace.{u2} β] {F : ι -> β -> α} {x₀ : β}, Iff (EquicontinuousAt.{u3, u2, u1} ι β α (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F x₀) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (x : β), (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) x x₀) δ) -> (forall (i : ι), LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (F i x₀) (F i x)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : PseudoMetricSpace.{u2} β] {F : ι -> β -> α} {x₀ : β}, Iff (EquicontinuousAt.{u3, u2, u1} ι β α (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F x₀) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (x : β), (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) x x₀) δ) -> (forall (i : ι), LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (F i x₀) (F i x)) ε)))))
Case conversion may be inaccurate. Consider using '#align metric.equicontinuous_at_iff Metric.equicontinuousAt_iffₓ'. -/
/-- Characterization of equicontinuity for families of functions between (pseudo) metric spaces. -/
theorem equicontinuousAt_iff {ι : Type _} [PseudoMetricSpace β] {F : ι → β → α} {x₀ : β} :
    EquicontinuousAt F x₀ ↔ ∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ i, dist (F i x₀) (F i x) < ε :=
  nhds_basis_ball.equicontinuousAt_iff uniformity_basis_dist
#align metric.equicontinuous_at_iff Metric.equicontinuousAt_iff

/- warning: metric.equicontinuous_at_iff_pair -> Metric.equicontinuousAt_iff_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {F : ι -> β -> α} {x₀ : β}, Iff (EquicontinuousAt.{u3, u2, u1} ι β α _inst_2 (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F x₀) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u2} (Set.{u2} β) (fun (U : Set.{u2} β) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) U (nhds.{u2} β _inst_2 x₀)) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) U (nhds.{u2} β _inst_2 x₀)) => forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x U) -> (forall (x' : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x' U) -> (forall (i : ι), LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (F i x) (F i x')) ε))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {F : ι -> β -> α} {x₀ : β}, Iff (EquicontinuousAt.{u3, u2, u1} ι β α _inst_2 (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F x₀) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u2} (Set.{u2} β) (fun (U : Set.{u2} β) => And (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) U (nhds.{u2} β _inst_2 x₀)) (forall (x : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x U) -> (forall (x' : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x' U) -> (forall (i : ι), LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (F i x) (F i x')) ε))))))
Case conversion may be inaccurate. Consider using '#align metric.equicontinuous_at_iff_pair Metric.equicontinuousAt_iff_pairₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x x' «expr ∈ » U) -/
/-- Reformulation of `equicontinuous_at_iff_pair` for families of functions taking values in a
(pseudo) metric space. -/
protected theorem equicontinuousAt_iff_pair {ι : Type _} [TopologicalSpace β] {F : ι → β → α}
    {x₀ : β} :
    EquicontinuousAt F x₀ ↔
      ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∀ (x) (_ : x ∈ U) (x') (_ : x' ∈ U), ∀ i, dist (F i x) (F i x') < ε :=
  by
  rw [equicontinuousAt_iff_pair]
  constructor <;> intro H
  · intro ε hε
    refine' Exists.imp (fun V => Exists.imp fun hV h => _) (H _ (dist_mem_uniformity hε))
    exact fun x hx x' hx' => h _ hx _ hx'
  · intro U hU
    rcases mem_uniformity_dist.mp hU with ⟨ε, hε, hεU⟩
    refine' Exists.imp (fun V => Exists.imp fun hV h => _) (H _ hε)
    exact fun x hx x' hx' i => hεU (h _ hx _ hx' i)
#align metric.equicontinuous_at_iff_pair Metric.equicontinuousAt_iff_pair

/- warning: metric.uniform_equicontinuous_iff_right -> Metric.uniformEquicontinuous_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : UniformSpace.{u2} β] {F : ι -> β -> α}, Iff (UniformEquicontinuous.{u3, u1, u2} ι α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_2 F) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Eventually.{u2} (Prod.{u2, u2} β β) (fun (xy : Prod.{u2, u2} β β) => forall (i : ι), LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (F i (Prod.fst.{u2, u2} β β xy)) (F i (Prod.snd.{u2, u2} β β xy))) ε) (uniformity.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : UniformSpace.{u2} β] {F : ι -> β -> α}, Iff (UniformEquicontinuous.{u3, u1, u2} ι α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_2 F) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Eventually.{u2} (Prod.{u2, u2} β β) (fun (xy : Prod.{u2, u2} β β) => forall (i : ι), LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (F i (Prod.fst.{u2, u2} β β xy)) (F i (Prod.snd.{u2, u2} β β xy))) ε) (uniformity.{u2} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align metric.uniform_equicontinuous_iff_right Metric.uniformEquicontinuous_iff_rightₓ'. -/
/-- Characterization of uniform equicontinuity for families of functions taking values in a
(pseudo) metric space. -/
theorem uniformEquicontinuous_iff_right {ι : Type _} [UniformSpace β] {F : ι → β → α} :
    UniformEquicontinuous F ↔ ∀ ε > 0, ∀ᶠ xy : β × β in 𝓤 β, ∀ i, dist (F i xy.1) (F i xy.2) < ε :=
  uniformity_basis_dist.uniformEquicontinuous_iff_right
#align metric.uniform_equicontinuous_iff_right Metric.uniformEquicontinuous_iff_right

/- warning: metric.uniform_equicontinuous_iff -> Metric.uniformEquicontinuous_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : PseudoMetricSpace.{u2} β] {F : ι -> β -> α}, Iff (UniformEquicontinuous.{u3, u1, u2} ι α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) F) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (x : β) (y : β), (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) x y) δ) -> (forall (i : ι), LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (F i x) (F i y)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : PseudoMetricSpace.{u2} β] {F : ι -> β -> α}, Iff (UniformEquicontinuous.{u3, u1, u2} ι α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) F) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (x : β) (y : β), (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) x y) δ) -> (forall (i : ι), LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (F i x) (F i y)) ε)))))
Case conversion may be inaccurate. Consider using '#align metric.uniform_equicontinuous_iff Metric.uniformEquicontinuous_iffₓ'. -/
/-- Characterization of uniform equicontinuity for families of functions between
(pseudo) metric spaces. -/
theorem uniformEquicontinuous_iff {ι : Type _} [PseudoMetricSpace β] {F : ι → β → α} :
    UniformEquicontinuous F ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → ∀ i, dist (F i x) (F i y) < ε :=
  uniformity_basis_dist.uniformEquicontinuous_iff uniformity_basis_dist
#align metric.uniform_equicontinuous_iff Metric.uniformEquicontinuous_iff

/- warning: metric.equicontinuous_at_of_continuity_modulus -> Metric.equicontinuousAt_of_continuity_modulus is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {x₀ : β} (b : β -> Real), (Filter.Tendsto.{u2, 0} β Real b (nhds.{u2} β _inst_2 x₀) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (forall (F : ι -> β -> α), (Filter.Eventually.{u2} β (fun (x : β) => forall (i : ι), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (F i x₀) (F i x)) (b x)) (nhds.{u2} β _inst_2 x₀)) -> (EquicontinuousAt.{u3, u2, u1} ι β α _inst_2 (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F x₀))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {x₀ : β} (b : β -> Real), (Filter.Tendsto.{u2, 0} β Real b (nhds.{u2} β _inst_2 x₀) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (forall (F : ι -> β -> α), (Filter.Eventually.{u2} β (fun (x : β) => forall (i : ι), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (F i x₀) (F i x)) (b x)) (nhds.{u2} β _inst_2 x₀)) -> (EquicontinuousAt.{u3, u2, u1} ι β α _inst_2 (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F x₀))
Case conversion may be inaccurate. Consider using '#align metric.equicontinuous_at_of_continuity_modulus Metric.equicontinuousAt_of_continuity_modulusₓ'. -/
/-- For a family of functions to a (pseudo) metric spaces, a convenient way to prove
equicontinuity at a point is to show that all of the functions share a common *local* continuity
modulus. -/
theorem equicontinuousAt_of_continuity_modulus {ι : Type _} [TopologicalSpace β] {x₀ : β}
    (b : β → ℝ) (b_lim : Tendsto b (𝓝 x₀) (𝓝 0)) (F : ι → β → α)
    (H : ∀ᶠ x in 𝓝 x₀, ∀ i, dist (F i x₀) (F i x) ≤ b x) : EquicontinuousAt F x₀ :=
  by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε ε0
  filter_upwards [b_lim (Iio_mem_nhds ε0), H]using fun x hx₁ hx₂ i => (hx₂ i).trans_lt hx₁
#align metric.equicontinuous_at_of_continuity_modulus Metric.equicontinuousAt_of_continuity_modulus

/- warning: metric.uniform_equicontinuous_of_continuity_modulus -> Metric.uniformEquicontinuous_of_continuity_modulus is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : PseudoMetricSpace.{u2} β] (b : Real -> Real), (Filter.Tendsto.{0, 0} Real Real b (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (forall (F : ι -> β -> α), (forall (x : β) (y : β) (i : ι), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (F i x) (F i y)) (b (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) x y))) -> (UniformEquicontinuous.{u3, u1, u2} ι α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) F))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : PseudoMetricSpace.{u2} β] (b : Real -> Real), (Filter.Tendsto.{0, 0} Real Real b (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (forall (F : ι -> β -> α), (forall (x : β) (y : β) (i : ι), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (F i x) (F i y)) (b (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) x y))) -> (UniformEquicontinuous.{u3, u1, u2} ι α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) F))
Case conversion may be inaccurate. Consider using '#align metric.uniform_equicontinuous_of_continuity_modulus Metric.uniformEquicontinuous_of_continuity_modulusₓ'. -/
/-- For a family of functions between (pseudo) metric spaces, a convenient way to prove
uniform equicontinuity is to show that all of the functions share a common *global* continuity
modulus. -/
theorem uniformEquicontinuous_of_continuity_modulus {ι : Type _} [PseudoMetricSpace β] (b : ℝ → ℝ)
    (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι → β → α)
    (H : ∀ (x y : β) (i), dist (F i x) (F i y) ≤ b (dist x y)) : UniformEquicontinuous F :=
  by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε ε0
  rcases tendsto_nhds_nhds.1 b_lim ε ε0 with ⟨δ, δ0, hδ⟩
  refine' ⟨δ, δ0, fun x y hxy i => _⟩
  calc
    dist (F i x) (F i y) ≤ b (dist x y) := H x y i
    _ ≤ |b (dist x y)| := (le_abs_self _)
    _ = dist (b (dist x y)) 0 := by simp [Real.dist_eq]
    _ < ε := hδ (by simpa only [Real.dist_eq, tsub_zero, abs_dist] using hxy)
    
#align metric.uniform_equicontinuous_of_continuity_modulus Metric.uniformEquicontinuous_of_continuity_modulus

/- warning: metric.equicontinuous_of_continuity_modulus -> Metric.equicontinuous_of_continuity_modulus is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : PseudoMetricSpace.{u2} β] (b : Real -> Real), (Filter.Tendsto.{0, 0} Real Real b (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (forall (F : ι -> β -> α), (forall (x : β) (y : β) (i : ι), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (F i x) (F i y)) (b (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) x y))) -> (Equicontinuous.{u3, u2, u1} ι β α (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : PseudoMetricSpace.{u2} β] (b : Real -> Real), (Filter.Tendsto.{0, 0} Real Real b (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (forall (F : ι -> β -> α), (forall (x : β) (y : β) (i : ι), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (F i x) (F i y)) (b (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) x y))) -> (Equicontinuous.{u3, u2, u1} ι β α (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F))
Case conversion may be inaccurate. Consider using '#align metric.equicontinuous_of_continuity_modulus Metric.equicontinuous_of_continuity_modulusₓ'. -/
/-- For a family of functions between (pseudo) metric spaces, a convenient way to prove
equicontinuity is to show that all of the functions share a common *global* continuity modulus. -/
theorem equicontinuous_of_continuity_modulus {ι : Type _} [PseudoMetricSpace β] (b : ℝ → ℝ)
    (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι → β → α)
    (H : ∀ (x y : β) (i), dist (F i x) (F i y) ≤ b (dist x y)) : Equicontinuous F :=
  (uniformEquicontinuous_of_continuity_modulus b b_lim F H).Equicontinuous
#align metric.equicontinuous_of_continuity_modulus Metric.equicontinuous_of_continuity_modulus

end Metric

