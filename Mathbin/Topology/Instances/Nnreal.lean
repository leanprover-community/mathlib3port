/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module topology.instances.nnreal
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.InfiniteSum.Order
import Mathbin.Topology.Algebra.InfiniteSum.Ring
import Mathbin.Topology.Instances.Real

/-!
# Topology on `ℝ≥0`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The natural topology on `ℝ≥0` (the one induced from `ℝ`), and a basic API.

## Main definitions

Instances for the following typeclasses are defined:

* `topological_space ℝ≥0`
* `topological_semiring ℝ≥0`
* `second_countable_topology ℝ≥0`
* `order_topology ℝ≥0`
* `has_continuous_sub ℝ≥0`
* `has_continuous_inv₀ ℝ≥0` (continuity of `x⁻¹` away from `0`)
* `has_continuous_smul ℝ≥0 α` (whenever `α` has a continuous `mul_action ℝ α`)

Everything is inherited from the corresponding structures on the reals.

## Main statements

Various mathematically trivial lemmas are proved about the compatibility
of limits and sums in `ℝ≥0` and `ℝ`. For example

* `tendsto_coe {f : filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
  tendsto (λa, (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ tendsto m f (𝓝 x)`

says that the limit of a filter along a map to `ℝ≥0` is the same in `ℝ` and `ℝ≥0`, and

* `coe_tsum {f : α → ℝ≥0} : ((∑'a, f a) : ℝ) = (∑'a, (f a : ℝ))`

says that says that a sum of elements in `ℝ≥0` is the same in `ℝ` and `ℝ≥0`.

Similarly, some mathematically trivial lemmas about infinite sums are proved,
a few of which rely on the fact that subtraction is continuous.

-/


noncomputable section

open Set TopologicalSpace Metric Filter

open Topology

namespace NNReal

open NNReal BigOperators Filter

instance : TopologicalSpace ℝ≥0 :=
  inferInstance

-- short-circuit type class inference
instance : TopologicalSemiring ℝ≥0
    where
  continuous_mul := (continuous_subtype_val.fst'.mul continuous_subtype_val.snd').subtype_mk _
  continuous_add := (continuous_subtype_val.fst'.add continuous_subtype_val.snd').subtype_mk _

instance : SecondCountableTopology ℝ≥0 :=
  TopologicalSpace.Subtype.secondCountableTopology _ _

instance : OrderTopology ℝ≥0 :=
  @orderTopology_of_ordConnected _ _ _ _ (Ici 0) _

section coe

variable {α : Type _}

open Filter Finset

/- warning: continuous_real_to_nnreal -> continuous_real_toNNReal is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} Real NNReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) NNReal.topologicalSpace Real.toNNReal
but is expected to have type
  Continuous.{0, 0} Real NNReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) NNReal.instTopologicalSpaceNNReal Real.toNNReal
Case conversion may be inaccurate. Consider using '#align continuous_real_to_nnreal continuous_real_toNNRealₓ'. -/
theorem continuous_real_toNNReal : Continuous Real.toNNReal :=
  (continuous_id.max continuous_const).subtype_mk _
#align continuous_real_to_nnreal continuous_real_toNNReal

/- warning: nnreal.continuous_coe -> NNReal.continuous_coe is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} NNReal Real NNReal.topologicalSpace (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))))
but is expected to have type
  Continuous.{0, 0} NNReal Real NNReal.instTopologicalSpaceNNReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) NNReal.toReal
Case conversion may be inaccurate. Consider using '#align nnreal.continuous_coe NNReal.continuous_coeₓ'. -/
theorem continuous_coe : Continuous (coe : ℝ≥0 → ℝ) :=
  continuous_subtype_val
#align nnreal.continuous_coe NNReal.continuous_coe

/- warning: continuous_map.coe_nnreal_real -> ContinuousMap.coeNNRealReal is a dubious translation:
lean 3 declaration is
  ContinuousMap.{0, 0} NNReal Real NNReal.topologicalSpace (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
but is expected to have type
  ContinuousMap.{0, 0} NNReal Real NNReal.instTopologicalSpaceNNReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_nnreal_real ContinuousMap.coeNNRealRealₓ'. -/
/-- Embedding of `ℝ≥0` to `ℝ` as a bundled continuous map. -/
@[simps (config := { fullyApplied := false })]
def ContinuousMap.coeNNRealReal : C(ℝ≥0, ℝ) :=
  ⟨coe, continuous_coe⟩
#align continuous_map.coe_nnreal_real ContinuousMap.coeNNRealReal

/- warning: nnreal.continuous_map.can_lift -> NNReal.ContinuousMap.canLift is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], CanLift.{succ u1, succ u1} (ContinuousMap.{u1, 0} X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (ContinuousMap.{u1, 0} X NNReal _inst_1 NNReal.topologicalSpace) (ContinuousMap.comp.{u1, 0, 0} X NNReal Real _inst_1 NNReal.topologicalSpace (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ContinuousMap.coeNNRealReal) (fun (f : ContinuousMap.{u1, 0} X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) => forall (x : X), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (coeFn.{succ u1, succ u1} (ContinuousMap.{u1, 0} X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (fun (_x : ContinuousMap.{u1, 0} X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) => X -> Real) (ContinuousMap.hasCoeToFun.{u1, 0} X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) f x))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], CanLift.{succ u1, succ u1} (ContinuousMap.{u1, 0} X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (ContinuousMap.{u1, 0} X NNReal _inst_1 NNReal.instTopologicalSpaceNNReal) (ContinuousMap.comp.{u1, 0, 0} X NNReal Real _inst_1 NNReal.instTopologicalSpaceNNReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ContinuousMap.coeNNRealReal) (fun (f : ContinuousMap.{u1, 0} X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) => forall (x : X), LE.le.{0} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : X) => Real) x) Real.instLEReal (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : X) => Real) x) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : X) => Real) x) Real.instZeroReal)) (FunLike.coe.{succ u1, succ u1, 1} (ContinuousMap.{u1, 0} X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : X) => Real) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (ContinuousMap.{u1, 0} X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (ContinuousMap.instContinuousMapClassContinuousMap.{u1, 0} X Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) f x))
Case conversion may be inaccurate. Consider using '#align nnreal.continuous_map.can_lift NNReal.ContinuousMap.canLiftₓ'. -/
instance ContinuousMap.canLift {X : Type _} [TopologicalSpace X] :
    CanLift C(X, ℝ) C(X, ℝ≥0) ContinuousMap.coeNNRealReal.comp fun f => ∀ x, 0 ≤ f x
    where prf f hf := ⟨⟨fun x => ⟨f x, hf x⟩, f.2.subtype_mk _⟩, FunLike.ext' rfl⟩
#align nnreal.continuous_map.can_lift NNReal.ContinuousMap.canLift

/- warning: nnreal.tendsto_coe -> NNReal.tendsto_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> NNReal} {x : NNReal}, Iff (Filter.Tendsto.{u1, 0} α Real (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (m a)) f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x))) (Filter.Tendsto.{u1, 0} α NNReal m f (nhds.{0} NNReal NNReal.topologicalSpace x))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> NNReal} {x : NNReal}, Iff (Filter.Tendsto.{u1, 0} α Real (fun (a : α) => NNReal.toReal (m a)) f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (NNReal.toReal x))) (Filter.Tendsto.{u1, 0} α NNReal m f (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal x))
Case conversion may be inaccurate. Consider using '#align nnreal.tendsto_coe NNReal.tendsto_coeₓ'. -/
@[simp, norm_cast]
theorem tendsto_coe {f : Filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
    Tendsto (fun a => (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ Tendsto m f (𝓝 x) :=
  tendsto_subtype_rng.symm
#align nnreal.tendsto_coe NNReal.tendsto_coe

/- warning: nnreal.tendsto_coe' -> NNReal.tendsto_coe' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : Filter.NeBot.{u1} α f] {m : α -> NNReal} {x : Real}, Iff (Filter.Tendsto.{u1, 0} α Real (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (m a)) f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) x)) (Exists.{0} (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (fun (hx : LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) => Filter.Tendsto.{u1, 0} α NNReal m f (nhds.{0} NNReal NNReal.topologicalSpace (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) x hx))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : Filter.NeBot.{u1} α f] {m : α -> NNReal} {x : Real}, Iff (Filter.Tendsto.{u1, 0} α Real (fun (a : α) => NNReal.toReal (m a)) f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) x)) (Exists.{0} (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) (fun (hx : LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) => Filter.Tendsto.{u1, 0} α NNReal m f (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) x hx))))
Case conversion may be inaccurate. Consider using '#align nnreal.tendsto_coe' NNReal.tendsto_coe'ₓ'. -/
theorem tendsto_coe' {f : Filter α} [NeBot f] {m : α → ℝ≥0} {x : ℝ} :
    Tendsto (fun a => m a : α → ℝ) f (𝓝 x) ↔ ∃ hx : 0 ≤ x, Tendsto m f (𝓝 ⟨x, hx⟩) :=
  ⟨fun h => ⟨ge_of_tendsto' h fun c => (m c).2, tendsto_coe.1 h⟩, fun ⟨hx, hm⟩ => tendsto_coe.2 hm⟩
#align nnreal.tendsto_coe' NNReal.tendsto_coe'

/- warning: nnreal.map_coe_at_top -> NNReal.map_coe_atTop is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} Real) (Filter.map.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (Filter.atTop.{0} Real Real.preorder)
but is expected to have type
  Eq.{1} (Filter.{0} Real) (Filter.map.{0, 0} NNReal Real NNReal.toReal (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)))) (Filter.atTop.{0} Real Real.instPreorderReal)
Case conversion may be inaccurate. Consider using '#align nnreal.map_coe_at_top NNReal.map_coe_atTopₓ'. -/
@[simp]
theorem map_coe_atTop : map (coe : ℝ≥0 → ℝ) atTop = atTop :=
  map_val_Ici_atTop 0
#align nnreal.map_coe_at_top NNReal.map_coe_atTop

/- warning: nnreal.comap_coe_at_top -> NNReal.comap_coe_atTop is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} NNReal) (Filter.comap.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) (Filter.atTop.{0} Real Real.preorder)) (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))
but is expected to have type
  Eq.{1} (Filter.{0} NNReal) (Filter.comap.{0, 0} NNReal Real NNReal.toReal (Filter.atTop.{0} Real Real.instPreorderReal)) (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)))
Case conversion may be inaccurate. Consider using '#align nnreal.comap_coe_at_top NNReal.comap_coe_atTopₓ'. -/
theorem comap_coe_atTop : comap (coe : ℝ≥0 → ℝ) atTop = atTop :=
  (atTop_Ici_eq 0).symm
#align nnreal.comap_coe_at_top NNReal.comap_coe_atTop

/- warning: nnreal.tendsto_coe_at_top -> NNReal.tendsto_coe_atTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> NNReal}, Iff (Filter.Tendsto.{u1, 0} α Real (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (m a)) f (Filter.atTop.{0} Real Real.preorder)) (Filter.Tendsto.{u1, 0} α NNReal m f (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> NNReal}, Iff (Filter.Tendsto.{u1, 0} α Real (fun (a : α) => NNReal.toReal (m a)) f (Filter.atTop.{0} Real Real.instPreorderReal)) (Filter.Tendsto.{u1, 0} α NNReal m f (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))))
Case conversion may be inaccurate. Consider using '#align nnreal.tendsto_coe_at_top NNReal.tendsto_coe_atTopₓ'. -/
@[simp, norm_cast]
theorem tendsto_coe_atTop {f : Filter α} {m : α → ℝ≥0} :
    Tendsto (fun a => (m a : ℝ)) f atTop ↔ Tendsto m f atTop :=
  tendsto_Ici_atTop.symm
#align nnreal.tendsto_coe_at_top NNReal.tendsto_coe_atTop

/- warning: tendsto_real_to_nnreal -> tendsto_real_toNNReal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> Real} {x : Real}, (Filter.Tendsto.{u1, 0} α Real m f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) x)) -> (Filter.Tendsto.{u1, 0} α NNReal (fun (a : α) => Real.toNNReal (m a)) f (nhds.{0} NNReal NNReal.topologicalSpace (Real.toNNReal x)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> Real} {x : Real}, (Filter.Tendsto.{u1, 0} α Real m f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) x)) -> (Filter.Tendsto.{u1, 0} α NNReal (fun (a : α) => Real.toNNReal (m a)) f (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal (Real.toNNReal x)))
Case conversion may be inaccurate. Consider using '#align tendsto_real_to_nnreal tendsto_real_toNNRealₓ'. -/
theorem tendsto_real_toNNReal {f : Filter α} {m : α → ℝ} {x : ℝ} (h : Tendsto m f (𝓝 x)) :
    Tendsto (fun a => Real.toNNReal (m a)) f (𝓝 (Real.toNNReal x)) :=
  (continuous_real_toNNReal.Tendsto _).comp h
#align tendsto_real_to_nnreal tendsto_real_toNNReal

#print tendsto_real_toNNReal_atTop /-
theorem tendsto_real_toNNReal_atTop : Tendsto Real.toNNReal atTop atTop :=
  by
  rw [← tendsto_coe_at_top]
  apply tendsto_id.congr' _
  filter_upwards [Ici_mem_at_top (0 : ℝ)]with x hx
  simp only [max_eq_left (Set.mem_Ici.1 hx), id.def, Real.coe_toNNReal']
#align tendsto_real_to_nnreal_at_top tendsto_real_toNNReal_atTop
-/

/- warning: nnreal.nhds_zero -> NNReal.nhds_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} NNReal) (nhds.{0} NNReal NNReal.topologicalSpace (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (infᵢ.{0, 1} (Filter.{0} NNReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} NNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} NNReal) (Filter.completeLattice.{0} NNReal))) NNReal (fun (a : NNReal) => infᵢ.{0, 0} (Filter.{0} NNReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} NNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} NNReal) (Filter.completeLattice.{0} NNReal))) (Ne.{1} NNReal a (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (fun (H : Ne.{1} NNReal a (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) => Filter.principal.{0} NNReal (Set.Iio.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a))))
but is expected to have type
  Eq.{1} (Filter.{0} NNReal) (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (infᵢ.{0, 1} (Filter.{0} NNReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} NNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} NNReal) (Filter.instCompleteLatticeFilter.{0} NNReal))) NNReal (fun (a : NNReal) => infᵢ.{0, 0} (Filter.{0} NNReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} NNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} NNReal) (Filter.instCompleteLatticeFilter.{0} NNReal))) (Ne.{1} NNReal a (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (fun (H : Ne.{1} NNReal a (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) => Filter.principal.{0} NNReal (Set.Iio.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a))))
Case conversion may be inaccurate. Consider using '#align nnreal.nhds_zero NNReal.nhds_zeroₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ≠ » 0) -/
theorem nhds_zero : 𝓝 (0 : ℝ≥0) = ⨅ (a) (_ : a ≠ 0), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp [bot_lt_iff_ne_bot]
#align nnreal.nhds_zero NNReal.nhds_zero

/- warning: nnreal.nhds_zero_basis -> NNReal.nhds_zero_basis is a dubious translation:
lean 3 declaration is
  Filter.HasBasis.{0, 1} NNReal NNReal (nhds.{0} NNReal NNReal.topologicalSpace (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (fun (a : NNReal) => LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) a) (fun (a : NNReal) => Set.Iio.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)
but is expected to have type
  Filter.HasBasis.{0, 1} NNReal NNReal (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (fun (a : NNReal) => LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) a) (fun (a : NNReal) => Set.Iio.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)
Case conversion may be inaccurate. Consider using '#align nnreal.nhds_zero_basis NNReal.nhds_zero_basisₓ'. -/
theorem nhds_zero_basis : (𝓝 (0 : ℝ≥0)).HasBasis (fun a : ℝ≥0 => 0 < a) fun a => Iio a :=
  nhds_bot_basis
#align nnreal.nhds_zero_basis NNReal.nhds_zero_basis

instance : ContinuousSub ℝ≥0 :=
  ⟨((continuous_coe.fst'.sub continuous_coe.snd').max continuous_const).subtype_mk _⟩

instance : HasContinuousInv₀ ℝ≥0 :=
  ⟨fun x hx =>
    tendsto_coe.1 <| (Real.tendsto_inv <| NNReal.coe_ne_zero.2 hx).comp continuous_coe.ContinuousAt⟩

instance [TopologicalSpace α] [MulAction ℝ α] [ContinuousSMul ℝ α] : ContinuousSMul ℝ≥0 α
    where continuous_smul := (continuous_induced_dom.comp continuous_fst).smul continuous_snd

/- warning: nnreal.has_sum_coe -> NNReal.hasSum_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal} {r : NNReal}, Iff (HasSum.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (f a)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r)) (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f r)
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal} {r : NNReal}, Iff (HasSum.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : α) => NNReal.toReal (f a)) (NNReal.toReal r)) (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f r)
Case conversion may be inaccurate. Consider using '#align nnreal.has_sum_coe NNReal.hasSum_coeₓ'. -/
@[norm_cast]
theorem hasSum_coe {f : α → ℝ≥0} {r : ℝ≥0} : HasSum (fun a => (f a : ℝ)) (r : ℝ) ↔ HasSum f r := by
  simp only [HasSum, coe_sum.symm, tendsto_coe]
#align nnreal.has_sum_coe NNReal.hasSum_coe

/- warning: nnreal.has_sum_real_to_nnreal_of_nonneg -> NNReal.hasSum_real_toNNReal_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> Real}, (forall (n : α), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f n)) -> (Summable.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (n : α) => Real.toNNReal (f n)) (Real.toNNReal (tsum.{0, u1} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (n : α) => f n))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> Real}, (forall (n : α), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f n)) -> (Summable.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (n : α) => Real.toNNReal (f n)) (Real.toNNReal (tsum.{0, u1} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (n : α) => f n))))
Case conversion may be inaccurate. Consider using '#align nnreal.has_sum_real_to_nnreal_of_nonneg NNReal.hasSum_real_toNNReal_of_nonnegₓ'. -/
theorem hasSum_real_toNNReal_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f) :
    HasSum (fun n => Real.toNNReal (f n)) (Real.toNNReal (∑' n, f n)) :=
  by
  have h_sum : (fun s => ∑ b in s, Real.toNNReal (f b)) = fun s => Real.toNNReal (∑ b in s, f b) :=
    funext fun _ => (Real.toNNReal_sum_of_nonneg fun n _ => hf_nonneg n).symm
  simp_rw [HasSum, h_sum]
  exact tendsto_real_toNNReal hf.has_sum
#align nnreal.has_sum_real_to_nnreal_of_nonneg NNReal.hasSum_real_toNNReal_of_nonneg

/- warning: nnreal.summable_coe -> NNReal.summable_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal}, Iff (Summable.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (f a))) (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f)
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal}, Iff (Summable.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : α) => NNReal.toReal (f a))) (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f)
Case conversion may be inaccurate. Consider using '#align nnreal.summable_coe NNReal.summable_coeₓ'. -/
@[norm_cast]
theorem summable_coe {f : α → ℝ≥0} : (Summable fun a => (f a : ℝ)) ↔ Summable f :=
  by
  constructor
  exact fun ⟨a, ha⟩ => ⟨⟨a, hasSum_le (fun a => (f a).2) hasSum_zero ha⟩, has_sum_coe.1 ha⟩
  exact fun ⟨a, ha⟩ => ⟨a.1, has_sum_coe.2 ha⟩
#align nnreal.summable_coe NNReal.summable_coe

/- warning: nnreal.summable_coe_of_nonneg -> NNReal.summable_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> Real} (hf₁ : forall (n : α), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f n)), Iff (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (n : α) => Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) (f n) (hf₁ n))) (Summable.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)
but is expected to have type
  forall {α : Type.{u1}} {f : α -> Real} (hf₁ : forall (n : α), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f n)), Iff (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (n : α) => Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) (f n) (hf₁ n))) (Summable.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)
Case conversion may be inaccurate. Consider using '#align nnreal.summable_coe_of_nonneg NNReal.summable_mkₓ'. -/
theorem summable_mk {f : α → ℝ} (hf₁ : ∀ n, 0 ≤ f n) :
    (@Summable ℝ≥0 _ _ _ fun n => ⟨f n, hf₁ n⟩) ↔ Summable f :=
  by
  lift f to α → ℝ≥0 using hf₁ with f rfl hf₁
  simp only [summable_coe, Subtype.coe_eta]
#align nnreal.summable_coe_of_nonneg NNReal.summable_mk

open Classical

/- warning: nnreal.coe_tsum -> NNReal.coe_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal}, Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (a : α) => f a))) (tsum.{0, u1} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (f a)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal}, Eq.{1} Real (NNReal.toReal (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (a : α) => f a))) (tsum.{0, u1} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (a : α) => NNReal.toReal (f a)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_tsum NNReal.coe_tsumₓ'. -/
@[norm_cast]
theorem coe_tsum {f : α → ℝ≥0} : ↑(∑' a, f a) = ∑' a, (f a : ℝ) :=
  if hf : Summable f then Eq.symm <| (hasSum_coe.2 <| hf.HasSum).tsum_eq
  else by simp [tsum, hf, mt summable_coe.1 hf]
#align nnreal.coe_tsum NNReal.coe_tsum

/- warning: nnreal.coe_tsum_of_nonneg -> NNReal.coe_tsum_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> Real} (hf₁ : forall (n : α), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f n)), Eq.{1} (Subtype.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r)) (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) (tsum.{0, u1} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (n : α) => f n)) (tsum_nonneg.{u1, 0} α Real Real.orderedAddCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OrderTopology.to_orderClosedTopology.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.linearOrder Real.orderTopology) (fun (n : α) => f n) hf₁)) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (n : α) => Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) (f n) (hf₁ n)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> Real} (hf₁ : forall (n : α), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f n)), Eq.{1} (Subtype.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r)) (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) (tsum.{0, u1} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (n : α) => f n)) (tsum_nonneg.{u1, 0} α Real Real.orderedAddCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OrderTopology.to_orderClosedTopology.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.linearOrder instOrderTopologyRealToTopologicalSpaceToUniformSpacePseudoMetricSpaceInstPreorderReal) (fun (n : α) => f n) hf₁)) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (n : α) => Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) (f n) (hf₁ n)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_tsum_of_nonneg NNReal.coe_tsum_of_nonnegₓ'. -/
theorem coe_tsum_of_nonneg {f : α → ℝ} (hf₁ : ∀ n, 0 ≤ f n) :
    (⟨∑' n, f n, tsum_nonneg hf₁⟩ : ℝ≥0) = (∑' n, ⟨f n, hf₁ n⟩ : ℝ≥0) :=
  by
  lift f to α → ℝ≥0 using hf₁ with f rfl hf₁
  simp_rw [← NNReal.coe_tsum, Subtype.coe_eta]
#align nnreal.coe_tsum_of_nonneg NNReal.coe_tsum_of_nonneg

/- warning: nnreal.tsum_mul_left -> NNReal.tsum_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : NNReal) (f : α -> NNReal), Eq.{1} NNReal (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (x : α) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a (f x))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (x : α) => f x)))
but is expected to have type
  forall {α : Type.{u1}} (a : NNReal) (f : α -> NNReal), Eq.{1} NNReal (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (x : α) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a (f x))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align nnreal.tsum_mul_left NNReal.tsum_mul_leftₓ'. -/
theorem tsum_mul_left (a : ℝ≥0) (f : α → ℝ≥0) : (∑' x, a * f x) = a * ∑' x, f x :=
  NNReal.eq <| by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_left]
#align nnreal.tsum_mul_left NNReal.tsum_mul_left

/- warning: nnreal.tsum_mul_right -> NNReal.tsum_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : α -> NNReal) (a : NNReal), Eq.{1} NNReal (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (x : α) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (f x) a)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (x : α) => f x)) a)
but is expected to have type
  forall {α : Type.{u1}} (f : α -> NNReal) (a : NNReal), Eq.{1} NNReal (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (x : α) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (f x) a)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (x : α) => f x)) a)
Case conversion may be inaccurate. Consider using '#align nnreal.tsum_mul_right NNReal.tsum_mul_rightₓ'. -/
theorem tsum_mul_right (f : α → ℝ≥0) (a : ℝ≥0) : (∑' x, f x * a) = (∑' x, f x) * a :=
  NNReal.eq <| by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_right]
#align nnreal.tsum_mul_right NNReal.tsum_mul_right

/- warning: nnreal.summable_comp_injective -> NNReal.summable_comp_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) -> (forall {i : β -> α}, (Function.Injective.{succ u2, succ u1} β α i) -> (Summable.{0, u2} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (Function.comp.{succ u2, succ u1, 1} β α NNReal f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) -> (forall {i : β -> α}, (Function.Injective.{succ u2, succ u1} β α i) -> (Summable.{0, u2} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (Function.comp.{succ u2, succ u1, 1} β α NNReal f i)))
Case conversion may be inaccurate. Consider using '#align nnreal.summable_comp_injective NNReal.summable_comp_injectiveₓ'. -/
theorem summable_comp_injective {β : Type _} {f : α → ℝ≥0} (hf : Summable f) {i : β → α}
    (hi : Function.Injective i) : Summable (f ∘ i) :=
  NNReal.summable_coe.1 <|
    show Summable ((coe ∘ f) ∘ i) from (NNReal.summable_coe.2 hf).comp_injective hi
#align nnreal.summable_comp_injective NNReal.summable_comp_injective

/- warning: nnreal.summable_nat_add -> NNReal.summable_nat_add is a dubious translation:
lean 3 declaration is
  forall (f : Nat -> NNReal), (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) -> (forall (k : Nat), Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i k)))
but is expected to have type
  forall (f : Nat -> NNReal), (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) -> (forall (k : Nat), Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i k)))
Case conversion may be inaccurate. Consider using '#align nnreal.summable_nat_add NNReal.summable_nat_addₓ'. -/
theorem summable_nat_add (f : ℕ → ℝ≥0) (hf : Summable f) (k : ℕ) : Summable fun i => f (i + k) :=
  summable_comp_injective hf <| add_left_injective k
#align nnreal.summable_nat_add NNReal.summable_nat_add

/- warning: nnreal.summable_nat_add_iff -> NNReal.summable_nat_add_iff is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> NNReal} (k : Nat), Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i k))) (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f)
but is expected to have type
  forall {f : Nat -> NNReal} (k : Nat), Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i k))) (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f)
Case conversion may be inaccurate. Consider using '#align nnreal.summable_nat_add_iff NNReal.summable_nat_add_iffₓ'. -/
theorem summable_nat_add_iff {f : ℕ → ℝ≥0} (k : ℕ) : (Summable fun i => f (i + k)) ↔ Summable f :=
  by
  rw [← summable_coe, ← summable_coe]
  exact @summable_nat_add_iff ℝ _ _ _ (fun i => (f i : ℝ)) k
#align nnreal.summable_nat_add_iff NNReal.summable_nat_add_iff

/- warning: nnreal.has_sum_nat_add_iff -> NNReal.hasSum_nat_add_iff is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> NNReal} (k : Nat) {a : NNReal}, Iff (HasSum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n k)) a) (HasSum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a (Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) (Finset.range k) (fun (i : Nat) => f i))))
but is expected to have type
  forall {f : Nat -> NNReal} (k : Nat) {a : NNReal}, Iff (HasSum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n k)) a) (HasSum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) a (Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) (Finset.range k) (fun (i : Nat) => f i))))
Case conversion may be inaccurate. Consider using '#align nnreal.has_sum_nat_add_iff NNReal.hasSum_nat_add_iffₓ'. -/
theorem hasSum_nat_add_iff {f : ℕ → ℝ≥0} (k : ℕ) {a : ℝ≥0} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) := by
  simp [← has_sum_coe, coe_sum, NNReal.coe_add, ← hasSum_nat_add_iff k]
#align nnreal.has_sum_nat_add_iff NNReal.hasSum_nat_add_iff

/- warning: nnreal.sum_add_tsum_nat_add -> NNReal.sum_add_tsum_nat_add is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> NNReal} (k : Nat), (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) -> (Eq.{1} NNReal (tsum.{0, 0} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace Nat (fun (i : Nat) => f i)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) (Finset.range k) (fun (i : Nat) => f i)) (tsum.{0, 0} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i k)))))
but is expected to have type
  forall {f : Nat -> NNReal} (k : Nat), (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) -> (Eq.{1} NNReal (tsum.{0, 0} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal Nat (fun (i : Nat) => f i)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) (Finset.range k) (fun (i : Nat) => f i)) (tsum.{0, 0} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i k)))))
Case conversion may be inaccurate. Consider using '#align nnreal.sum_add_tsum_nat_add NNReal.sum_add_tsum_nat_addₓ'. -/
theorem sum_add_tsum_nat_add {f : ℕ → ℝ≥0} (k : ℕ) (hf : Summable f) :
    (∑' i, f i) = (∑ i in range k, f i) + ∑' i, f (i + k) := by
  rw [← NNReal.coe_eq, coe_tsum, NNReal.coe_add, coe_sum, coe_tsum,
    sum_add_tsum_nat_add k (NNReal.summable_coe.2 hf)]
#align nnreal.sum_add_tsum_nat_add NNReal.sum_add_tsum_nat_add

/- warning: nnreal.infi_real_pos_eq_infi_nnreal_pos -> NNReal.infᵢ_real_pos_eq_infᵢ_nNReal_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Real -> α}, Eq.{succ u1} α (infᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Real (fun (n : Real) => infᵢ.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) n) (fun (h : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) n) => f n))) (infᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) NNReal (fun (n : NNReal) => infᵢ.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) n) (fun (h : LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) n) => f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Real -> α}, Eq.{succ u1} α (infᵢ.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Real (fun (n : Real) => infᵢ.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) n) (fun (h : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) n) => f n))) (infᵢ.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) NNReal (fun (n : NNReal) => infᵢ.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) n) (fun (h : LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) n) => f (NNReal.toReal n))))
Case conversion may be inaccurate. Consider using '#align nnreal.infi_real_pos_eq_infi_nnreal_pos NNReal.infᵢ_real_pos_eq_infᵢ_nNReal_posₓ'. -/
theorem infᵢ_real_pos_eq_infᵢ_nNReal_pos [CompleteLattice α] {f : ℝ → α} :
    (⨅ (n : ℝ) (h : 0 < n), f n) = ⨅ (n : ℝ≥0) (h : 0 < n), f n :=
  le_antisymm (infᵢ_mono' fun r => ⟨r, le_rfl⟩) (infᵢ₂_mono' fun r hr => ⟨⟨r, hr.le⟩, hr, le_rfl⟩)
#align nnreal.infi_real_pos_eq_infi_nnreal_pos NNReal.infᵢ_real_pos_eq_infᵢ_nNReal_pos

end coe

/- warning: nnreal.tendsto_cofinite_zero_of_summable -> NNReal.tendsto_cofinite_zero_of_summable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) -> (Filter.Tendsto.{u1, 0} α NNReal f (Filter.cofinite.{u1} α) (nhds.{0} NNReal NNReal.topologicalSpace (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) -> (Filter.Tendsto.{u1, 0} α NNReal f (Filter.cofinite.{u1} α) (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))))
Case conversion may be inaccurate. Consider using '#align nnreal.tendsto_cofinite_zero_of_summable NNReal.tendsto_cofinite_zero_of_summableₓ'. -/
theorem tendsto_cofinite_zero_of_summable {α} {f : α → ℝ≥0} (hf : Summable f) :
    Tendsto f cofinite (𝓝 0) :=
  by
  have h_f_coe : f = fun n => Real.toNNReal (f n : ℝ) := funext fun n => real.to_nnreal_coe.symm
  rw [h_f_coe, ← @Real.toNNReal_coe 0]
  exact tendsto_real_toNNReal (summable_coe.mpr hf).tendsto_cofinite_zero
#align nnreal.tendsto_cofinite_zero_of_summable NNReal.tendsto_cofinite_zero_of_summable

/- warning: nnreal.tendsto_at_top_zero_of_summable -> NNReal.tendsto_atTop_zero_of_summable is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> NNReal}, (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) -> (Filter.Tendsto.{0, 0} Nat NNReal f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} NNReal NNReal.topologicalSpace (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))))
but is expected to have type
  forall {f : Nat -> NNReal}, (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) -> (Filter.Tendsto.{0, 0} Nat NNReal f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))))
Case conversion may be inaccurate. Consider using '#align nnreal.tendsto_at_top_zero_of_summable NNReal.tendsto_atTop_zero_of_summableₓ'. -/
theorem tendsto_atTop_zero_of_summable {f : ℕ → ℝ≥0} (hf : Summable f) : Tendsto f atTop (𝓝 0) :=
  by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_summable hf
#align nnreal.tendsto_at_top_zero_of_summable NNReal.tendsto_atTop_zero_of_summable

/- warning: nnreal.tendsto_tsum_compl_at_top_zero -> NNReal.tendsto_tsum_compl_atTop_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : α -> NNReal), Filter.Tendsto.{u1, 0} (Finset.{u1} α) NNReal (fun (s : Finset.{u1} α) => tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (fun (b : Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) α (coeSubtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)))))) b))) (Filter.atTop.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (nhds.{0} NNReal NNReal.topologicalSpace (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {α : Type.{u1}} (f : α -> NNReal), Filter.Tendsto.{u1, 0} (Finset.{u1} α) NNReal (fun (s : Finset.{u1} α) => tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (Subtype.{succ u1} α (fun (x : α) => Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s))) (fun (b : Subtype.{succ u1} α (fun (x : α) => Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s))) => f (Subtype.val.{succ u1} α (fun (x : α) => Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s)) b))) (Filter.atTop.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)))
Case conversion may be inaccurate. Consider using '#align nnreal.tendsto_tsum_compl_at_top_zero NNReal.tendsto_tsum_compl_atTop_zeroₓ'. -/
/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_atTop_zero {α : Type _} (f : α → ℝ≥0) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) :=
  by
  simp_rw [← tendsto_coe, coe_tsum, NNReal.coe_zero]
  exact tendsto_tsum_compl_atTop_zero fun a : α => (f a : ℝ)
#align nnreal.tendsto_tsum_compl_at_top_zero NNReal.tendsto_tsum_compl_atTop_zero

#print NNReal.powOrderIso /-
/-- `x ↦ x ^ n` as an order isomorphism of `ℝ≥0`. -/
def powOrderIso (n : ℕ) (hn : n ≠ 0) : ℝ≥0 ≃o ℝ≥0 :=
  (StrictMono.orderIsoOfSurjective (fun x => x ^ n) fun x y h =>
      strictMonoOn_pow hn.bot_lt (zero_le x) (zero_le y) h) <|
    (continuous_id.pow _).Surjective (tendsto_pow_atTop hn) <| by
      simpa [order_bot.at_bot_eq, pos_iff_ne_zero]
#align nnreal.pow_order_iso NNReal.powOrderIso
-/

end NNReal

