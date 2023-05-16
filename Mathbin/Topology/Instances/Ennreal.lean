/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module topology.instances.ennreal
! leanprover-community/mathlib commit ec4b2eeb50364487f80421c0b4c41328a611f30d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Instances.Nnreal
import Mathbin.Topology.Algebra.Order.MonotoneContinuity
import Mathbin.Topology.Algebra.InfiniteSum.Real
import Mathbin.Topology.Algebra.Order.LiminfLimsup
import Mathbin.Topology.MetricSpace.Lipschitz

/-!
# Extended non-negative reals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


noncomputable section

open Classical Set Filter Metric

open Classical Topology ENNReal NNReal BigOperators Filter

variable {α : Type _} {β : Type _} {γ : Type _}

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

variable {x y z : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞} {s : Set ℝ≥0∞}

section TopologicalSpace

open TopologicalSpace

/-- Topology on `ℝ≥0∞`.

Note: this is different from the `emetric_space` topology. The `emetric_space` topology has
`is_open {⊤}`, while this topology doesn't have singleton elements. -/
instance : TopologicalSpace ℝ≥0∞ :=
  Preorder.topology ℝ≥0∞

instance : OrderTopology ℝ≥0∞ :=
  ⟨rfl⟩

instance : T2Space ℝ≥0∞ := by infer_instance

-- short-circuit type class inference
instance : NormalSpace ℝ≥0∞ :=
  normalOfCompactT2

instance : SecondCountableTopology ℝ≥0∞ :=
  orderIsoUnitIntervalBirational.toHomeomorph.Embedding.SecondCountableTopology

/- warning: ennreal.embedding_coe -> ENNReal.embedding_coe is a dubious translation:
lean 3 declaration is
  Embedding.{0, 0} NNReal ENNReal NNReal.topologicalSpace ENNReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))))
but is expected to have type
  Embedding.{0, 0} NNReal ENNReal NNReal.instTopologicalSpaceNNReal ENNReal.instTopologicalSpaceENNReal ENNReal.some
Case conversion may be inaccurate. Consider using '#align ennreal.embedding_coe ENNReal.embedding_coeₓ'. -/
theorem embedding_coe : Embedding (coe : ℝ≥0 → ℝ≥0∞) :=
  ⟨⟨by
      refine' le_antisymm _ _
      · rw [@OrderTopology.topology_eq_generate_intervals ℝ≥0∞ _, ← coinduced_le_iff_le_induced]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        show IsOpen { b : ℝ≥0 | a < ↑b }
        · cases a <;> simp [none_eq_top, some_eq_coe, isOpen_lt']
        show IsOpen { b : ℝ≥0 | ↑b < a }
        · cases a <;> simp [none_eq_top, some_eq_coe, isOpen_gt', isOpen_const]
      · rw [@OrderTopology.topology_eq_generate_intervals ℝ≥0 _]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        exact ⟨Ioi a, isOpen_Ioi, by simp [Ioi]⟩
        exact ⟨Iio a, isOpen_Iio, by simp [Iio]⟩⟩, fun a b => coe_eq_coe.1⟩
#align ennreal.embedding_coe ENNReal.embedding_coe

/- warning: ennreal.is_open_ne_top -> ENNReal.isOpen_ne_top is a dubious translation:
lean 3 declaration is
  IsOpen.{0} ENNReal ENNReal.topologicalSpace (setOf.{0} ENNReal (fun (a : ENNReal) => Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  IsOpen.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (setOf.{0} ENNReal (fun (a : ENNReal) => Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align ennreal.is_open_ne_top ENNReal.isOpen_ne_topₓ'. -/
theorem isOpen_ne_top : IsOpen { a : ℝ≥0∞ | a ≠ ⊤ } :=
  isOpen_ne
#align ennreal.is_open_ne_top ENNReal.isOpen_ne_top

/- warning: ennreal.is_open_Ico_zero -> ENNReal.isOpen_Ico_zero is a dubious translation:
lean 3 declaration is
  forall {b : ENNReal}, IsOpen.{0} ENNReal ENNReal.topologicalSpace (Set.Ico.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) b)
but is expected to have type
  forall {b : ENNReal}, IsOpen.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Set.Ico.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) b)
Case conversion may be inaccurate. Consider using '#align ennreal.is_open_Ico_zero ENNReal.isOpen_Ico_zeroₓ'. -/
theorem isOpen_Ico_zero : IsOpen (Ico 0 b) :=
  by
  rw [ENNReal.Ico_eq_Iio]
  exact isOpen_Iio
#align ennreal.is_open_Ico_zero ENNReal.isOpen_Ico_zero

/- warning: ennreal.open_embedding_coe -> ENNReal.openEmbedding_coe is a dubious translation:
lean 3 declaration is
  OpenEmbedding.{0, 0} NNReal ENNReal NNReal.topologicalSpace ENNReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))))
but is expected to have type
  OpenEmbedding.{0, 0} NNReal ENNReal NNReal.instTopologicalSpaceNNReal ENNReal.instTopologicalSpaceENNReal ENNReal.some
Case conversion may be inaccurate. Consider using '#align ennreal.open_embedding_coe ENNReal.openEmbedding_coeₓ'. -/
theorem openEmbedding_coe : OpenEmbedding (coe : ℝ≥0 → ℝ≥0∞) :=
  ⟨embedding_coe, by
    convert is_open_ne_top
    ext (x | _) <;> simp [none_eq_top, some_eq_coe]⟩
#align ennreal.open_embedding_coe ENNReal.openEmbedding_coe

/- warning: ennreal.coe_range_mem_nhds -> ENNReal.coe_range_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {r : NNReal}, Membership.Mem.{0, 0} (Set.{0} ENNReal) (Filter.{0} ENNReal) (Filter.hasMem.{0} ENNReal) (Set.range.{0, 1} ENNReal NNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))))) (nhds.{0} ENNReal ENNReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) r))
but is expected to have type
  forall {r : NNReal}, Membership.mem.{0, 0} (Set.{0} ENNReal) (Filter.{0} ENNReal) (instMembershipSetFilter.{0} ENNReal) (Set.range.{0, 1} ENNReal NNReal ENNReal.some) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (ENNReal.some r))
Case conversion may be inaccurate. Consider using '#align ennreal.coe_range_mem_nhds ENNReal.coe_range_mem_nhdsₓ'. -/
theorem coe_range_mem_nhds : range (coe : ℝ≥0 → ℝ≥0∞) ∈ 𝓝 (r : ℝ≥0∞) :=
  IsOpen.mem_nhds openEmbedding_coe.open_range <| mem_range_self _
#align ennreal.coe_range_mem_nhds ENNReal.coe_range_mem_nhds

/- warning: ennreal.tendsto_coe -> ENNReal.tendsto_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> NNReal} {a : NNReal}, Iff (Filter.Tendsto.{u1, 0} α ENNReal (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (m a)) f (nhds.{0} ENNReal ENNReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) a))) (Filter.Tendsto.{u1, 0} α NNReal m f (nhds.{0} NNReal NNReal.topologicalSpace a))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> NNReal} {a : NNReal}, Iff (Filter.Tendsto.{u1, 0} α ENNReal (fun (a : α) => ENNReal.some (m a)) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (ENNReal.some a))) (Filter.Tendsto.{u1, 0} α NNReal m f (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal a))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_coe ENNReal.tendsto_coeₓ'. -/
@[norm_cast]
theorem tendsto_coe {f : Filter α} {m : α → ℝ≥0} {a : ℝ≥0} :
    Tendsto (fun a => (m a : ℝ≥0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe.tendsto_nhds_iff.symm
#align ennreal.tendsto_coe ENNReal.tendsto_coe

/- warning: ennreal.continuous_coe -> ENNReal.continuous_coe is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} NNReal ENNReal NNReal.topologicalSpace ENNReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))))
but is expected to have type
  Continuous.{0, 0} NNReal ENNReal NNReal.instTopologicalSpaceNNReal ENNReal.instTopologicalSpaceENNReal ENNReal.some
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_coe ENNReal.continuous_coeₓ'. -/
theorem continuous_coe : Continuous (coe : ℝ≥0 → ℝ≥0∞) :=
  embedding_coe.Continuous
#align ennreal.continuous_coe ENNReal.continuous_coe

/- warning: ennreal.continuous_coe_iff -> ENNReal.continuous_coe_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> NNReal}, Iff (Continuous.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f a))) (Continuous.{u1, 0} α NNReal _inst_1 NNReal.topologicalSpace f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> NNReal}, Iff (Continuous.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal (fun (a : α) => ENNReal.some (f a))) (Continuous.{u1, 0} α NNReal _inst_1 NNReal.instTopologicalSpaceNNReal f)
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_coe_iff ENNReal.continuous_coe_iffₓ'. -/
theorem continuous_coe_iff {α} [TopologicalSpace α] {f : α → ℝ≥0} :
    (Continuous fun a => (f a : ℝ≥0∞)) ↔ Continuous f :=
  embedding_coe.continuous_iff.symm
#align ennreal.continuous_coe_iff ENNReal.continuous_coe_iff

/- warning: ennreal.nhds_coe -> ENNReal.nhds_coe is a dubious translation:
lean 3 declaration is
  forall {r : NNReal}, Eq.{1} (Filter.{0} ENNReal) (nhds.{0} ENNReal ENNReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) r)) (Filter.map.{0, 0} NNReal ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe)))) (nhds.{0} NNReal NNReal.topologicalSpace r))
but is expected to have type
  forall {r : NNReal}, Eq.{1} (Filter.{0} ENNReal) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (ENNReal.some r)) (Filter.map.{0, 0} NNReal ENNReal ENNReal.some (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal r))
Case conversion may be inaccurate. Consider using '#align ennreal.nhds_coe ENNReal.nhds_coeₓ'. -/
theorem nhds_coe {r : ℝ≥0} : 𝓝 (r : ℝ≥0∞) = (𝓝 r).map coe :=
  (openEmbedding_coe.map_nhds_eq r).symm
#align ennreal.nhds_coe ENNReal.nhds_coe

/- warning: ennreal.tendsto_nhds_coe_iff -> ENNReal.tendsto_nhds_coe_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {x : NNReal} {f : ENNReal -> α}, Iff (Filter.Tendsto.{0, u1} ENNReal α f (nhds.{0} ENNReal ENNReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) x)) l) (Filter.Tendsto.{0, u1} NNReal α (Function.comp.{1, 1, succ u1} NNReal ENNReal α f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))))) (nhds.{0} NNReal NNReal.topologicalSpace x) l)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {x : NNReal} {f : ENNReal -> α}, Iff (Filter.Tendsto.{0, u1} ENNReal α f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (ENNReal.some x)) l) (Filter.Tendsto.{0, u1} NNReal α (Function.comp.{1, 1, succ u1} NNReal ENNReal α f ENNReal.some) (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal x) l)
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_nhds_coe_iff ENNReal.tendsto_nhds_coe_iffₓ'. -/
theorem tendsto_nhds_coe_iff {α : Type _} {l : Filter α} {x : ℝ≥0} {f : ℝ≥0∞ → α} :
    Tendsto f (𝓝 ↑x) l ↔ Tendsto (f ∘ coe : ℝ≥0 → α) (𝓝 x) l :=
  show _ ≤ _ ↔ _ ≤ _ by rw [nhds_coe, Filter.map_map]
#align ennreal.tendsto_nhds_coe_iff ENNReal.tendsto_nhds_coe_iff

/- warning: ennreal.continuous_at_coe_iff -> ENNReal.continuousAt_coe_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : NNReal} {f : ENNReal -> α}, Iff (ContinuousAt.{0, u1} ENNReal α ENNReal.topologicalSpace _inst_1 f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) x)) (ContinuousAt.{0, u1} NNReal α NNReal.topologicalSpace _inst_1 (Function.comp.{1, 1, succ u1} NNReal ENNReal α f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))))) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : NNReal} {f : ENNReal -> α}, Iff (ContinuousAt.{0, u1} ENNReal α ENNReal.instTopologicalSpaceENNReal _inst_1 f (ENNReal.some x)) (ContinuousAt.{0, u1} NNReal α NNReal.instTopologicalSpaceNNReal _inst_1 (Function.comp.{1, 1, succ u1} NNReal ENNReal α f ENNReal.some) x)
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_at_coe_iff ENNReal.continuousAt_coe_iffₓ'. -/
theorem continuousAt_coe_iff {α : Type _} [TopologicalSpace α] {x : ℝ≥0} {f : ℝ≥0∞ → α} :
    ContinuousAt f ↑x ↔ ContinuousAt (f ∘ coe : ℝ≥0 → α) x :=
  tendsto_nhds_coe_iff
#align ennreal.continuous_at_coe_iff ENNReal.continuousAt_coe_iff

/- warning: ennreal.nhds_coe_coe -> ENNReal.nhds_coe_coe is a dubious translation:
lean 3 declaration is
  forall {r : NNReal} {p : NNReal}, Eq.{1} (Filter.{0} (Prod.{0, 0} ENNReal ENNReal)) (nhds.{0} (Prod.{0, 0} ENNReal ENNReal) (Prod.topologicalSpace.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace) (Prod.mk.{0, 0} ENNReal ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) p))) (Filter.map.{0, 0} (Prod.{0, 0} NNReal NNReal) (Prod.{0, 0} ENNReal ENNReal) (fun (p : Prod.{0, 0} NNReal NNReal) => Prod.mk.{0, 0} ENNReal ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (Prod.fst.{0, 0} NNReal NNReal p)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (Prod.snd.{0, 0} NNReal NNReal p))) (nhds.{0} (Prod.{0, 0} NNReal NNReal) (Prod.topologicalSpace.{0, 0} NNReal NNReal NNReal.topologicalSpace NNReal.topologicalSpace) (Prod.mk.{0, 0} NNReal NNReal r p)))
but is expected to have type
  forall {r : NNReal} {p : NNReal}, Eq.{1} (Filter.{0} (Prod.{0, 0} ENNReal ENNReal)) (nhds.{0} (Prod.{0, 0} ENNReal ENNReal) (instTopologicalSpaceProd.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal) (Prod.mk.{0, 0} ENNReal ENNReal (ENNReal.some r) (ENNReal.some p))) (Filter.map.{0, 0} (Prod.{0, 0} NNReal NNReal) (Prod.{0, 0} ENNReal ENNReal) (fun (p : Prod.{0, 0} NNReal NNReal) => Prod.mk.{0, 0} ENNReal ENNReal (ENNReal.some (Prod.fst.{0, 0} NNReal NNReal p)) (ENNReal.some (Prod.snd.{0, 0} NNReal NNReal p))) (nhds.{0} (Prod.{0, 0} NNReal NNReal) (instTopologicalSpaceProd.{0, 0} NNReal NNReal NNReal.instTopologicalSpaceNNReal NNReal.instTopologicalSpaceNNReal) (Prod.mk.{0, 0} NNReal NNReal r p)))
Case conversion may be inaccurate. Consider using '#align ennreal.nhds_coe_coe ENNReal.nhds_coe_coeₓ'. -/
theorem nhds_coe_coe {r p : ℝ≥0} :
    𝓝 ((r : ℝ≥0∞), (p : ℝ≥0∞)) = (𝓝 (r, p)).map fun p : ℝ≥0 × ℝ≥0 => (p.1, p.2) :=
  ((openEmbedding_coe.Prod openEmbedding_coe).map_nhds_eq (r, p)).symm
#align ennreal.nhds_coe_coe ENNReal.nhds_coe_coe

/- warning: ennreal.continuous_of_real -> ENNReal.continuous_ofReal is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} Real ENNReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ENNReal.topologicalSpace ENNReal.ofReal
but is expected to have type
  Continuous.{0, 0} Real ENNReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ENNReal.instTopologicalSpaceENNReal ENNReal.ofReal
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_of_real ENNReal.continuous_ofRealₓ'. -/
theorem continuous_ofReal : Continuous ENNReal.ofReal :=
  (continuous_coe_iff.2 continuous_id).comp continuous_real_toNNReal
#align ennreal.continuous_of_real ENNReal.continuous_ofReal

/- warning: ennreal.tendsto_of_real -> ENNReal.tendsto_ofReal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> Real} {a : Real}, (Filter.Tendsto.{u1, 0} α Real m f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) a)) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (a : α) => ENNReal.ofReal (m a)) f (nhds.{0} ENNReal ENNReal.topologicalSpace (ENNReal.ofReal a)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> Real} {a : Real}, (Filter.Tendsto.{u1, 0} α Real m f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) a)) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (a : α) => ENNReal.ofReal (m a)) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (ENNReal.ofReal a)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_of_real ENNReal.tendsto_ofRealₓ'. -/
theorem tendsto_ofReal {f : Filter α} {m : α → ℝ} {a : ℝ} (h : Tendsto m f (𝓝 a)) :
    Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 (ENNReal.ofReal a)) :=
  Tendsto.comp (Continuous.tendsto continuous_ofReal _) h
#align ennreal.tendsto_of_real ENNReal.tendsto_ofReal

/- warning: ennreal.tendsto_to_nnreal -> ENNReal.tendsto_toNNReal is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Tendsto.{0, 0} ENNReal NNReal ENNReal.toNNReal (nhds.{0} ENNReal ENNReal.topologicalSpace a) (nhds.{0} NNReal NNReal.topologicalSpace (ENNReal.toNNReal a)))
but is expected to have type
  forall {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Tendsto.{0, 0} ENNReal NNReal ENNReal.toNNReal (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a) (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal (ENNReal.toNNReal a)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_to_nnreal ENNReal.tendsto_toNNRealₓ'. -/
theorem tendsto_toNNReal {a : ℝ≥0∞} (ha : a ≠ ⊤) : Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal) :=
  by
  lift a to ℝ≥0 using ha
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id
#align ennreal.tendsto_to_nnreal ENNReal.tendsto_toNNReal

/- warning: ennreal.eventually_eq_of_to_real_eventually_eq -> ENNReal.eventuallyEq_of_toReal_eventuallyEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> ENNReal} {g : α -> ENNReal}, (Filter.Eventually.{u1} α (fun (x : α) => Ne.{1} ENNReal (f x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) l) -> (Filter.Eventually.{u1} α (fun (x : α) => Ne.{1} ENNReal (g x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) l) -> (Filter.EventuallyEq.{u1, 0} α Real l (fun (x : α) => ENNReal.toReal (f x)) (fun (x : α) => ENNReal.toReal (g x))) -> (Filter.EventuallyEq.{u1, 0} α ENNReal l f g)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> ENNReal} {g : α -> ENNReal}, (Filter.Eventually.{u1} α (fun (x : α) => Ne.{1} ENNReal (f x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) l) -> (Filter.Eventually.{u1} α (fun (x : α) => Ne.{1} ENNReal (g x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) l) -> (Filter.EventuallyEq.{u1, 0} α Real l (fun (x : α) => ENNReal.toReal (f x)) (fun (x : α) => ENNReal.toReal (g x))) -> (Filter.EventuallyEq.{u1, 0} α ENNReal l f g)
Case conversion may be inaccurate. Consider using '#align ennreal.eventually_eq_of_to_real_eventually_eq ENNReal.eventuallyEq_of_toReal_eventuallyEqₓ'. -/
theorem eventuallyEq_of_toReal_eventuallyEq {l : Filter α} {f g : α → ℝ≥0∞}
    (hfi : ∀ᶠ x in l, f x ≠ ∞) (hgi : ∀ᶠ x in l, g x ≠ ∞)
    (hfg : (fun x => (f x).toReal) =ᶠ[l] fun x => (g x).toReal) : f =ᶠ[l] g :=
  by
  filter_upwards [hfi, hgi, hfg]with _ hfx hgx _
  rwa [← ENNReal.toReal_eq_toReal hfx hgx]
#align ennreal.eventually_eq_of_to_real_eventually_eq ENNReal.eventuallyEq_of_toReal_eventuallyEq

/- warning: ennreal.continuous_on_to_nnreal -> ENNReal.continuousOn_toNNReal is a dubious translation:
lean 3 declaration is
  ContinuousOn.{0, 0} ENNReal NNReal ENNReal.topologicalSpace NNReal.topologicalSpace ENNReal.toNNReal (setOf.{0} ENNReal (fun (a : ENNReal) => Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  ContinuousOn.{0, 0} ENNReal NNReal ENNReal.instTopologicalSpaceENNReal NNReal.instTopologicalSpaceNNReal ENNReal.toNNReal (setOf.{0} ENNReal (fun (a : ENNReal) => Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_on_to_nnreal ENNReal.continuousOn_toNNRealₓ'. -/
theorem continuousOn_toNNReal : ContinuousOn ENNReal.toNNReal { a | a ≠ ∞ } := fun a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toNNReal ha)
#align ennreal.continuous_on_to_nnreal ENNReal.continuousOn_toNNReal

/- warning: ennreal.tendsto_to_real -> ENNReal.tendsto_toReal is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Tendsto.{0, 0} ENNReal Real ENNReal.toReal (nhds.{0} ENNReal ENNReal.topologicalSpace a) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (ENNReal.toReal a)))
but is expected to have type
  forall {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Tendsto.{0, 0} ENNReal Real ENNReal.toReal (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (ENNReal.toReal a)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_to_real ENNReal.tendsto_toRealₓ'. -/
theorem tendsto_toReal {a : ℝ≥0∞} (ha : a ≠ ⊤) : Tendsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal) :=
  NNReal.tendsto_coe.2 <| tendsto_toNNReal ha
#align ennreal.tendsto_to_real ENNReal.tendsto_toReal

/- warning: ennreal.ne_top_homeomorph_nnreal -> ENNReal.neTopHomeomorphNNReal is a dubious translation:
lean 3 declaration is
  Homeomorph.{0, 0} (coeSort.{1, 2} (Set.{0} ENNReal) Type (Set.hasCoeToSort.{0} ENNReal) (setOf.{0} ENNReal (fun (a : ENNReal) => Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) NNReal (Subtype.topologicalSpace.{0} ENNReal (fun (x : ENNReal) => Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) x (setOf.{0} ENNReal (fun (a : ENNReal) => Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) ENNReal.topologicalSpace) NNReal.topologicalSpace
but is expected to have type
  Homeomorph.{0, 0} (Set.Elem.{0} ENNReal (setOf.{0} ENNReal (fun (a : ENNReal) => Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) NNReal (instTopologicalSpaceSubtype.{0} ENNReal (fun (x : ENNReal) => Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) x (setOf.{0} ENNReal (fun (a : ENNReal) => Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) ENNReal.instTopologicalSpaceENNReal) NNReal.instTopologicalSpaceNNReal
Case conversion may be inaccurate. Consider using '#align ennreal.ne_top_homeomorph_nnreal ENNReal.neTopHomeomorphNNRealₓ'. -/
/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def neTopHomeomorphNNReal : { a | a ≠ ∞ } ≃ₜ ℝ≥0 :=
  {
    neTopEquivNNReal with
    continuous_toFun := continuousOn_iff_continuous_restrict.1 continuousOn_toNNReal
    continuous_invFun := continuous_coe.subtype_mk _ }
#align ennreal.ne_top_homeomorph_nnreal ENNReal.neTopHomeomorphNNReal

/- warning: ennreal.lt_top_homeomorph_nnreal -> ENNReal.ltTopHomeomorphNNReal is a dubious translation:
lean 3 declaration is
  Homeomorph.{0, 0} (coeSort.{1, 2} (Set.{0} ENNReal) Type (Set.hasCoeToSort.{0} ENNReal) (setOf.{0} ENNReal (fun (a : ENNReal) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) NNReal (Subtype.topologicalSpace.{0} ENNReal (fun (x : ENNReal) => Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) x (setOf.{0} ENNReal (fun (a : ENNReal) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) ENNReal.topologicalSpace) NNReal.topologicalSpace
but is expected to have type
  Homeomorph.{0, 0} (Set.Elem.{0} ENNReal (setOf.{0} ENNReal (fun (a : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) NNReal (instTopologicalSpaceSubtype.{0} ENNReal (fun (x : ENNReal) => Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) x (setOf.{0} ENNReal (fun (a : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) ENNReal.instTopologicalSpaceENNReal) NNReal.instTopologicalSpaceNNReal
Case conversion may be inaccurate. Consider using '#align ennreal.lt_top_homeomorph_nnreal ENNReal.ltTopHomeomorphNNRealₓ'. -/
/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def ltTopHomeomorphNNReal : { a | a < ∞ } ≃ₜ ℝ≥0 := by
  refine' (Homeomorph.setCongr <| Set.ext fun x => _).trans ne_top_homeomorph_nnreal <;>
    simp only [mem_set_of_eq, lt_top_iff_ne_top]
#align ennreal.lt_top_homeomorph_nnreal ENNReal.ltTopHomeomorphNNReal

/- warning: ennreal.nhds_top -> ENNReal.nhds_top is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} ENNReal) (nhds.{0} ENNReal ENNReal.topologicalSpace (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (iInf.{0, 1} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.completeLattice.{0} ENNReal))) ENNReal (fun (a : ENNReal) => iInf.{0, 0} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.completeLattice.{0} ENNReal))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (fun (H : Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) => Filter.principal.{0} ENNReal (Set.Ioi.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) a))))
but is expected to have type
  Eq.{1} (Filter.{0} ENNReal) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (iInf.{0, 1} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.instCompleteLatticeFilter.{0} ENNReal))) ENNReal (fun (a : ENNReal) => iInf.{0, 0} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.instCompleteLatticeFilter.{0} ENNReal))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (fun (H : Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) => Filter.principal.{0} ENNReal (Set.Ioi.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) a))))
Case conversion may be inaccurate. Consider using '#align ennreal.nhds_top ENNReal.nhds_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ≠ » ennreal.top()) -/
theorem nhds_top : 𝓝 ∞ = ⨅ (a) (_ : a ≠ ∞), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp [lt_top_iff_ne_top, Ioi]
#align ennreal.nhds_top ENNReal.nhds_top

/- warning: ennreal.nhds_top' -> ENNReal.nhds_top' is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} ENNReal) (nhds.{0} ENNReal ENNReal.topologicalSpace (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (iInf.{0, 1} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.completeLattice.{0} ENNReal))) NNReal (fun (r : NNReal) => Filter.principal.{0} ENNReal (Set.Ioi.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) r))))
but is expected to have type
  Eq.{1} (Filter.{0} ENNReal) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (iInf.{0, 1} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.instCompleteLatticeFilter.{0} ENNReal))) NNReal (fun (r : NNReal) => Filter.principal.{0} ENNReal (Set.Ioi.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (ENNReal.some r))))
Case conversion may be inaccurate. Consider using '#align ennreal.nhds_top' ENNReal.nhds_top'ₓ'. -/
theorem nhds_top' : 𝓝 ∞ = ⨅ r : ℝ≥0, 𝓟 (Ioi r) :=
  nhds_top.trans <| iInf_ne_top _
#align ennreal.nhds_top' ENNReal.nhds_top'

/- warning: ennreal.nhds_top_basis -> ENNReal.nhds_top_basis is a dubious translation:
lean 3 declaration is
  Filter.HasBasis.{0, 1} ENNReal ENNReal (nhds.{0} ENNReal ENNReal.topologicalSpace (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (fun (a : ENNReal) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (fun (a : ENNReal) => Set.Ioi.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) a)
but is expected to have type
  Filter.HasBasis.{0, 1} ENNReal ENNReal (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (fun (a : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (fun (a : ENNReal) => Set.Ioi.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) a)
Case conversion may be inaccurate. Consider using '#align ennreal.nhds_top_basis ENNReal.nhds_top_basisₓ'. -/
theorem nhds_top_basis : (𝓝 ∞).HasBasis (fun a => a < ∞) fun a => Ioi a :=
  nhds_top_basis
#align ennreal.nhds_top_basis ENNReal.nhds_top_basis

/- warning: ennreal.tendsto_nhds_top_iff_nnreal -> ENNReal.tendsto_nhds_top_iff_nnreal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : α -> ENNReal} {f : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.topologicalSpace (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (forall (x : NNReal), Filter.Eventually.{u1} α (fun (a : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) x) (m a)) f)
but is expected to have type
  forall {α : Type.{u1}} {m : α -> ENNReal} {f : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (forall (x : NNReal), Filter.Eventually.{u1} α (fun (a : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENNReal.some x) (m a)) f)
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_nhds_top_iff_nnreal ENNReal.tendsto_nhds_top_iff_nnrealₓ'. -/
theorem tendsto_nhds_top_iff_nnreal {m : α → ℝ≥0∞} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ≥0, ∀ᶠ a in f, ↑x < m a := by
  simp only [nhds_top', tendsto_infi, tendsto_principal, mem_Ioi]
#align ennreal.tendsto_nhds_top_iff_nnreal ENNReal.tendsto_nhds_top_iff_nnreal

/- warning: ennreal.tendsto_nhds_top_iff_nat -> ENNReal.tendsto_nhds_top_iff_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : α -> ENNReal} {f : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.topologicalSpace (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (forall (n : Nat), Filter.Eventually.{u1} α (fun (a : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENNReal (HasLiftT.mk.{1, 1} Nat ENNReal (CoeTCₓ.coe.{1, 1} Nat ENNReal (Nat.castCoe.{0} ENNReal (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) n) (m a)) f)
but is expected to have type
  forall {α : Type.{u1}} {m : α -> ENNReal} {f : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (forall (n : Nat), Filter.Eventually.{u1} α (fun (a : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Nat.cast.{0} ENNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) n) (m a)) f)
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_nhds_top_iff_nat ENNReal.tendsto_nhds_top_iff_natₓ'. -/
theorem tendsto_nhds_top_iff_nat {m : α → ℝ≥0∞} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a :=
  tendsto_nhds_top_iff_nnreal.trans
    ⟨fun h n => by simpa only [ENNReal.coe_nat] using h n, fun h x =>
      let ⟨n, hn⟩ := exists_nat_gt x
      (h n).mono fun y => lt_trans <| by rwa [← ENNReal.coe_nat, coe_lt_coe]⟩
#align ennreal.tendsto_nhds_top_iff_nat ENNReal.tendsto_nhds_top_iff_nat

/- warning: ennreal.tendsto_nhds_top -> ENNReal.tendsto_nhds_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : α -> ENNReal} {f : Filter.{u1} α}, (forall (n : Nat), Filter.Eventually.{u1} α (fun (a : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENNReal (HasLiftT.mk.{1, 1} Nat ENNReal (CoeTCₓ.coe.{1, 1} Nat ENNReal (Nat.castCoe.{0} ENNReal (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) n) (m a)) f) -> (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.topologicalSpace (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u1}} {m : α -> ENNReal} {f : Filter.{u1} α}, (forall (n : Nat), Filter.Eventually.{u1} α (fun (a : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Nat.cast.{0} ENNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) n) (m a)) f) -> (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_nhds_top ENNReal.tendsto_nhds_topₓ'. -/
theorem tendsto_nhds_top {m : α → ℝ≥0∞} {f : Filter α} (h : ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a) :
    Tendsto m f (𝓝 ⊤) :=
  tendsto_nhds_top_iff_nat.2 h
#align ennreal.tendsto_nhds_top ENNReal.tendsto_nhds_top

/- warning: ennreal.tendsto_nat_nhds_top -> ENNReal.tendsto_nat_nhds_top is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENNReal (HasLiftT.mk.{1, 1} Nat ENNReal (CoeTCₓ.coe.{1, 1} Nat ENNReal (Nat.castCoe.{0} ENNReal (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) n) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => Nat.cast.{0} ENNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) n) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_nat_nhds_top ENNReal.tendsto_nat_nhds_topₓ'. -/
theorem tendsto_nat_nhds_top : Tendsto (fun n : ℕ => ↑n) atTop (𝓝 ∞) :=
  tendsto_nhds_top fun n =>
    mem_atTop_sets.2 ⟨n + 1, fun m hm => mem_setOf.2 <| Nat.cast_lt.2 <| Nat.lt_of_succ_le hm⟩
#align ennreal.tendsto_nat_nhds_top ENNReal.tendsto_nat_nhds_top

/- warning: ennreal.tendsto_coe_nhds_top -> ENNReal.tendsto_coe_nhds_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f x)) l (nhds.{0} ENNReal ENNReal.topologicalSpace (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Filter.Tendsto.{u1, 0} α NNReal f l (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => ENNReal.some (f x)) l (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Filter.Tendsto.{u1, 0} α NNReal f l (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_coe_nhds_top ENNReal.tendsto_coe_nhds_topₓ'. -/
@[simp, norm_cast]
theorem tendsto_coe_nhds_top {f : α → ℝ≥0} {l : Filter α} :
    Tendsto (fun x => (f x : ℝ≥0∞)) l (𝓝 ∞) ↔ Tendsto f l atTop := by
  rw [tendsto_nhds_top_iff_nnreal, at_top_basis_Ioi.tendsto_right_iff] <;> [simp, infer_instance,
    infer_instance]
#align ennreal.tendsto_coe_nhds_top ENNReal.tendsto_coe_nhds_top

/- warning: ennreal.tendsto_of_real_at_top -> ENNReal.tendsto_ofReal_atTop is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real ENNReal ENNReal.ofReal (Filter.atTop.{0} Real Real.preorder) (nhds.{0} ENNReal ENNReal.topologicalSpace (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  Filter.Tendsto.{0, 0} Real ENNReal ENNReal.ofReal (Filter.atTop.{0} Real Real.instPreorderReal) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_of_real_at_top ENNReal.tendsto_ofReal_atTopₓ'. -/
theorem tendsto_ofReal_atTop : Tendsto ENNReal.ofReal atTop (𝓝 ∞) :=
  tendsto_coe_nhds_top.2 tendsto_real_toNNReal_atTop
#align ennreal.tendsto_of_real_at_top ENNReal.tendsto_ofReal_atTop

/- warning: ennreal.nhds_zero -> ENNReal.nhds_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} ENNReal) (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (iInf.{0, 1} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.completeLattice.{0} ENNReal))) ENNReal (fun (a : ENNReal) => iInf.{0, 0} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.completeLattice.{0} ENNReal))) (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => Filter.principal.{0} ENNReal (Set.Iio.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) a))))
but is expected to have type
  Eq.{1} (Filter.{0} ENNReal) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (iInf.{0, 1} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.instCompleteLatticeFilter.{0} ENNReal))) ENNReal (fun (a : ENNReal) => iInf.{0, 0} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.instCompleteLatticeFilter.{0} ENNReal))) (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (fun (H : Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) => Filter.principal.{0} ENNReal (Set.Iio.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) a))))
Case conversion may be inaccurate. Consider using '#align ennreal.nhds_zero ENNReal.nhds_zeroₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ≠ » 0) -/
theorem nhds_zero : 𝓝 (0 : ℝ≥0∞) = ⨅ (a) (_ : a ≠ 0), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp [bot_lt_iff_ne_bot, Iio]
#align ennreal.nhds_zero ENNReal.nhds_zero

/- warning: ennreal.nhds_zero_basis -> ENNReal.nhds_zero_basis is a dubious translation:
lean 3 declaration is
  Filter.HasBasis.{0, 1} ENNReal ENNReal (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (a : ENNReal) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) a) (fun (a : ENNReal) => Set.Iio.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) a)
but is expected to have type
  Filter.HasBasis.{0, 1} ENNReal ENNReal (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (fun (a : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) a) (fun (a : ENNReal) => Set.Iio.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) a)
Case conversion may be inaccurate. Consider using '#align ennreal.nhds_zero_basis ENNReal.nhds_zero_basisₓ'. -/
theorem nhds_zero_basis : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) fun a => Iio a :=
  nhds_bot_basis
#align ennreal.nhds_zero_basis ENNReal.nhds_zero_basis

/- warning: ennreal.nhds_zero_basis_Iic -> ENNReal.nhds_zero_basis_Iic is a dubious translation:
lean 3 declaration is
  Filter.HasBasis.{0, 1} ENNReal ENNReal (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (a : ENNReal) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) a) (Set.Iic.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  Filter.HasBasis.{0, 1} ENNReal ENNReal (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (fun (a : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) a) (Set.Iic.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align ennreal.nhds_zero_basis_Iic ENNReal.nhds_zero_basis_Iicₓ'. -/
theorem nhds_zero_basis_Iic : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) Iic :=
  nhds_bot_basis_Iic
#align ennreal.nhds_zero_basis_Iic ENNReal.nhds_zero_basis_Iic

/- warning: ennreal.nhds_within_Ioi_coe_ne_bot -> ENNReal.nhdsWithin_Ioi_coe_neBot is a dubious translation:
lean 3 declaration is
  forall {r : NNReal}, Filter.NeBot.{0} ENNReal (nhdsWithin.{0} ENNReal ENNReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) r) (Set.Ioi.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) r)))
but is expected to have type
  forall {r : NNReal}, Filter.NeBot.{0} ENNReal (nhdsWithin.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (ENNReal.some r) (Set.Ioi.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (ENNReal.some r)))
Case conversion may be inaccurate. Consider using '#align ennreal.nhds_within_Ioi_coe_ne_bot ENNReal.nhdsWithin_Ioi_coe_neBotₓ'. -/
@[instance]
theorem nhdsWithin_Ioi_coe_neBot {r : ℝ≥0} : (𝓝[>] (r : ℝ≥0∞)).ne_bot :=
  nhdsWithin_Ioi_self_neBot' ⟨⊤, ENNReal.coe_lt_top⟩
#align ennreal.nhds_within_Ioi_coe_ne_bot ENNReal.nhdsWithin_Ioi_coe_neBot

/- warning: ennreal.nhds_within_Ioi_zero_ne_bot -> ENNReal.nhdsWithin_Ioi_zero_neBot is a dubious translation:
lean 3 declaration is
  Filter.NeBot.{0} ENNReal (nhdsWithin.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (Set.Ioi.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  Filter.NeBot.{0} ENNReal (nhdsWithin.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (Set.Ioi.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align ennreal.nhds_within_Ioi_zero_ne_bot ENNReal.nhdsWithin_Ioi_zero_neBotₓ'. -/
@[instance]
theorem nhdsWithin_Ioi_zero_neBot : (𝓝[>] (0 : ℝ≥0∞)).ne_bot :=
  nhdsWithin_Ioi_coe_neBot
#align ennreal.nhds_within_Ioi_zero_ne_bot ENNReal.nhdsWithin_Ioi_zero_neBot

/- warning: ennreal.Icc_mem_nhds -> ENNReal.Icc_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {ε : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Membership.Mem.{0, 0} (Set.{0} ENNReal) (Filter.{0} ENNReal) (Filter.hasMem.{0} ENNReal) (Set.Icc.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) x ε) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x ε)) (nhds.{0} ENNReal ENNReal.topologicalSpace x))
but is expected to have type
  forall {x : ENNReal} {ε : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Membership.mem.{0, 0} (Set.{0} ENNReal) (Filter.{0} ENNReal) (instMembershipSetFilter.{0} ENNReal) (Set.Icc.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) x ε) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) x ε)) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal x))
Case conversion may be inaccurate. Consider using '#align ennreal.Icc_mem_nhds ENNReal.Icc_mem_nhdsₓ'. -/
-- using Icc because
-- • don't have 'Ioo (x - ε) (x + ε) ∈ 𝓝 x' unless x > 0
-- • (x - y ≤ ε ↔ x ≤ ε + y) is true, while (x - y < ε ↔ x < ε + y) is not
theorem Icc_mem_nhds (xt : x ≠ ⊤) (ε0 : ε ≠ 0) : Icc (x - ε) (x + ε) ∈ 𝓝 x :=
  by
  rw [_root_.mem_nhds_iff]
  by_cases x0 : x = 0
  · use Iio (x + ε)
    have : Iio (x + ε) ⊆ Icc (x - ε) (x + ε)
    intro a
    rw [x0]
    simpa using le_of_lt
    use this
    exact ⟨isOpen_Iio, mem_Iio_self_add xt ε0⟩
  · use Ioo (x - ε) (x + ε)
    use Ioo_subset_Icc_self
    exact ⟨isOpen_Ioo, mem_Ioo_self_sub_add xt x0 ε0 ε0⟩
#align ennreal.Icc_mem_nhds ENNReal.Icc_mem_nhds

/- warning: ennreal.nhds_of_ne_top -> ENNReal.nhds_of_ne_top is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} (Filter.{0} ENNReal) (nhds.{0} ENNReal ENNReal.topologicalSpace x) (iInf.{0, 1} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.completeLattice.{0} ENNReal))) ENNReal (fun (ε : ENNReal) => iInf.{0, 0} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.completeLattice.{0} ENNReal))) (GT.gt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => Filter.principal.{0} ENNReal (Set.Icc.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) x ε) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x ε))))))
but is expected to have type
  forall {x : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} (Filter.{0} ENNReal) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal x) (iInf.{0, 1} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.instCompleteLatticeFilter.{0} ENNReal))) ENNReal (fun (ε : ENNReal) => iInf.{0, 0} (Filter.{0} ENNReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} ENNReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} ENNReal) (Filter.instCompleteLatticeFilter.{0} ENNReal))) (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) => Filter.principal.{0} ENNReal (Set.Icc.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) x ε) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) x ε))))))
Case conversion may be inaccurate. Consider using '#align ennreal.nhds_of_ne_top ENNReal.nhds_of_ne_topₓ'. -/
theorem nhds_of_ne_top (xt : x ≠ ⊤) : 𝓝 x = ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) :=
  by
  refine' le_antisymm _ _
  -- first direction
  simp only [le_iInf_iff, le_principal_iff];
  intro ε ε0; exact Icc_mem_nhds xt ε0.lt.ne'
  -- second direction
  rw [nhds_generate_from];
  refine' le_iInf fun s => le_iInf fun hs => _
  rcases hs with ⟨xs, ⟨a, (rfl : s = Ioi a) | (rfl : s = Iio a)⟩⟩
  · rcases exists_between xs with ⟨b, ab, bx⟩
    have xb_pos : 0 < x - b := tsub_pos_iff_lt.2 bx
    have xxb : x - (x - b) = b := sub_sub_cancel xt bx.le
    refine' iInf_le_of_le (x - b) (iInf_le_of_le xb_pos _)
    simp only [mem_principal, le_principal_iff]
    intro y
    rintro ⟨h₁, h₂⟩
    rw [xxb] at h₁
    calc
      a < b := ab
      _ ≤ y := h₁
      
  · rcases exists_between xs with ⟨b, xb, ba⟩
    have bx_pos : 0 < b - x := tsub_pos_iff_lt.2 xb
    have xbx : x + (b - x) = b := add_tsub_cancel_of_le xb.le
    refine' iInf_le_of_le (b - x) (iInf_le_of_le bx_pos _)
    simp only [mem_principal, le_principal_iff]
    intro y
    rintro ⟨h₁, h₂⟩
    rw [xbx] at h₂
    calc
      y ≤ b := h₂
      _ < a := ba
      
#align ennreal.nhds_of_ne_top ENNReal.nhds_of_ne_top

/- warning: ennreal.tendsto_nhds -> ENNReal.tendsto_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {u : α -> ENNReal} {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Iff (Filter.Tendsto.{u1, 0} α ENNReal u f (nhds.{0} ENNReal ENNReal.topologicalSpace a)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Filter.Eventually.{u1} α (fun (x : α) => Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) (u x) (Set.Icc.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) a ε) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a ε))) f)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {u : α -> ENNReal} {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Iff (Filter.Tendsto.{u1, 0} α ENNReal u f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Filter.Eventually.{u1} α (fun (x : α) => Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) (u x) (Set.Icc.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) a ε) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) a ε))) f)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_nhds ENNReal.tendsto_nhdsₓ'. -/
/-- Characterization of neighborhoods for `ℝ≥0∞` numbers. See also `tendsto_order`
for a version with strict inequalities. -/
protected theorem tendsto_nhds {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, u x ∈ Icc (a - ε) (a + ε) := by
  simp only [nhds_of_ne_top ha, tendsto_infi, tendsto_principal, mem_Icc]
#align ennreal.tendsto_nhds ENNReal.tendsto_nhds

/- warning: ennreal.tendsto_nhds_zero -> ENNReal.tendsto_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {u : α -> ENNReal}, Iff (Filter.Tendsto.{u1, 0} α ENNReal u f (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (u x) ε) f))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {u : α -> ENNReal}, Iff (Filter.Tendsto.{u1, 0} α ENNReal u f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (u x) ε) f))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_nhds_zero ENNReal.tendsto_nhds_zeroₓ'. -/
protected theorem tendsto_nhds_zero {f : Filter α} {u : α → ℝ≥0∞} :
    Tendsto u f (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ x in f, u x ≤ ε :=
  by
  rw [ENNReal.tendsto_nhds zero_ne_top]
  simp only [true_and_iff, zero_tsub, zero_le, zero_add, Set.mem_Icc]
#align ennreal.tendsto_nhds_zero ENNReal.tendsto_nhds_zero

/- warning: ennreal.tendsto_at_top -> ENNReal.tendsto_atTop is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : Nonempty.{succ u1} β] [_inst_2 : SemilatticeSup.{u1} β] {f : β -> ENNReal} {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Iff (Filter.Tendsto.{u1, 0} β ENNReal f (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_2))) (nhds.{0} ENNReal ENNReal.topologicalSpace a)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} β (fun (N : β) => forall (n : β), (GE.ge.{u1} β (Preorder.toHasLe.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_2))) n N) -> (Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) (f n) (Set.Icc.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) a ε) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a ε)))))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : Nonempty.{succ u1} β] [_inst_2 : SemilatticeSup.{u1} β] {f : β -> ENNReal} {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Iff (Filter.Tendsto.{u1, 0} β ENNReal f (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_2))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} β (fun (N : β) => forall (n : β), (GE.ge.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_2))) n N) -> (Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) (f n) (Set.Icc.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) a ε) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) a ε)))))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_at_top ENNReal.tendsto_atTopₓ'. -/
protected theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} {a : ℝ≥0∞}
    (ha : a ≠ ⊤) : Tendsto f atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ∈ Icc (a - ε) (a + ε) := by
  simp only [ENNReal.tendsto_nhds ha, mem_at_top_sets, mem_set_of_eq, Filter.Eventually]
#align ennreal.tendsto_at_top ENNReal.tendsto_atTop

instance : ContinuousAdd ℝ≥0∞ :=
  by
  refine' ⟨continuous_iff_continuousAt.2 _⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  simp only [ContinuousAt, some_eq_coe, nhds_coe_coe, ← coe_add, tendsto_map'_iff, (· ∘ ·),
    tendsto_coe, tendsto_add]

/- warning: ennreal.tendsto_at_top_zero -> ENNReal.tendsto_atTop_zero is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [hβ : Nonempty.{succ u1} β] [_inst_1 : SemilatticeSup.{u1} β] {f : β -> ENNReal}, Iff (Filter.Tendsto.{u1, 0} β ENNReal f (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_1))) (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} β (fun (N : β) => forall (n : β), (GE.ge.{u1} β (Preorder.toHasLe.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_1))) n N) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f n) ε))))
but is expected to have type
  forall {β : Type.{u1}} [hβ : Nonempty.{succ u1} β] [_inst_1 : SemilatticeSup.{u1} β] {f : β -> ENNReal}, Iff (Filter.Tendsto.{u1, 0} β ENNReal f (Filter.atTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_1))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} β (fun (N : β) => forall (n : β), (GE.ge.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_1))) n N) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f n) ε))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_at_top_zero ENNReal.tendsto_atTop_zeroₓ'. -/
protected theorem tendsto_atTop_zero [hβ : Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} :
    Filter.atTop.Tendsto f (𝓝 0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ ε :=
  by
  rw [ENNReal.tendsto_atTop zero_ne_top]
  · simp_rw [Set.mem_Icc, zero_add, zero_tsub, zero_le _, true_and_iff]
  · exact hβ
#align ennreal.tendsto_at_top_zero ENNReal.tendsto_atTop_zero

/- warning: ennreal.tendsto_sub -> ENNReal.tendsto_sub is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {b : ENNReal}, (Or (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Filter.Tendsto.{0, 0} (Prod.{0, 0} ENNReal ENNReal) ENNReal (fun (p : Prod.{0, 0} ENNReal ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (Prod.fst.{0, 0} ENNReal ENNReal p) (Prod.snd.{0, 0} ENNReal ENNReal p)) (nhds.{0} (Prod.{0, 0} ENNReal ENNReal) (Prod.topologicalSpace.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace) (Prod.mk.{0, 0} ENNReal ENNReal a b)) (nhds.{0} ENNReal ENNReal.topologicalSpace (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) a b)))
but is expected to have type
  forall {a : ENNReal} {b : ENNReal}, (Or (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Filter.Tendsto.{0, 0} (Prod.{0, 0} ENNReal ENNReal) ENNReal (fun (p : Prod.{0, 0} ENNReal ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (Prod.fst.{0, 0} ENNReal ENNReal p) (Prod.snd.{0, 0} ENNReal ENNReal p)) (nhds.{0} (Prod.{0, 0} ENNReal ENNReal) (instTopologicalSpaceProd.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal) (Prod.mk.{0, 0} ENNReal ENNReal a b)) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_sub ENNReal.tendsto_subₓ'. -/
theorem tendsto_sub {a b : ℝ≥0∞} (h : a ≠ ∞ ∨ b ≠ ∞) :
    Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 - p.2) (𝓝 (a, b)) (𝓝 (a - b)) :=
  by
  cases a <;> cases b
  · simp only [eq_self_iff_true, not_true, Ne.def, none_eq_top, or_self_iff] at h
    contradiction
  · simp only [some_eq_coe, WithTop.top_sub_coe, none_eq_top]
    apply tendsto_nhds_top_iff_nnreal.2 fun n => _
    rw [nhds_prod_eq, eventually_prod_iff]
    refine'
      ⟨fun z => (n + (b + 1) : ℝ≥0∞) < z,
        Ioi_mem_nhds (by simp only [one_lt_top, add_lt_top, coe_lt_top, and_self_iff]), fun z =>
        z < b + 1, Iio_mem_nhds (ENNReal.lt_add_right coe_ne_top one_ne_zero), fun x hx y hy => _⟩
    dsimp
    rw [lt_tsub_iff_right]
    have : (n : ℝ≥0∞) + y + (b + 1) < x + (b + 1) :=
      calc
        (n : ℝ≥0∞) + y + (b + 1) = (n : ℝ≥0∞) + (b + 1) + y := by abel
        _ < x + (b + 1) := ENNReal.add_lt_add hx hy
        
    exact lt_of_add_lt_add_right this
  · simp only [some_eq_coe, WithTop.sub_top, none_eq_top]
    suffices H : ∀ᶠ p : ℝ≥0∞ × ℝ≥0∞ in 𝓝 (a, ∞), 0 = p.1 - p.2
    exact tendsto_const_nhds.congr' H
    rw [nhds_prod_eq, eventually_prod_iff]
    refine'
      ⟨fun z => z < a + 1, Iio_mem_nhds (ENNReal.lt_add_right coe_ne_top one_ne_zero), fun z =>
        (a : ℝ≥0∞) + 1 < z,
        Ioi_mem_nhds (by simp only [one_lt_top, add_lt_top, coe_lt_top, and_self_iff]),
        fun x hx y hy => _⟩
    rw [eq_comm]
    simp only [tsub_eq_zero_iff_le, (LT.lt.trans hx hy).le]
  · simp only [some_eq_coe, nhds_coe_coe, tendsto_map'_iff, Function.comp, ← ENNReal.coe_sub,
      tendsto_coe]
    exact Continuous.tendsto (by continuity) _
#align ennreal.tendsto_sub ENNReal.tendsto_sub

/- warning: ennreal.tendsto.sub -> ENNReal.Tendsto.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {ma : α -> ENNReal} {mb : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal ma f (nhds.{0} ENNReal ENNReal.topologicalSpace a)) -> (Filter.Tendsto.{u1, 0} α ENNReal mb f (nhds.{0} ENNReal ENNReal.topologicalSpace b)) -> (Or (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (a : α) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (ma a) (mb a)) f (nhds.{0} ENNReal ENNReal.topologicalSpace (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) a b)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {ma : α -> ENNReal} {mb : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal ma f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a)) -> (Filter.Tendsto.{u1, 0} α ENNReal mb f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal b)) -> (Or (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (a : α) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (ma a) (mb a)) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto.sub ENNReal.Tendsto.subₓ'. -/
protected theorem Tendsto.sub {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (hmb : Tendsto mb f (𝓝 b)) (h : a ≠ ∞ ∨ b ≠ ∞) :
    Tendsto (fun a => ma a - mb a) f (𝓝 (a - b)) :=
  show Tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 - p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a - b)) from
    Tendsto.comp (ENNReal.tendsto_sub h) (hma.prod_mk_nhds hmb)
#align ennreal.tendsto.sub ENNReal.Tendsto.sub

/- warning: ennreal.tendsto_mul -> ENNReal.tendsto_mul is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {b : ENNReal}, (Or (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Or (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Filter.Tendsto.{0, 0} (Prod.{0, 0} ENNReal ENNReal) ENNReal (fun (p : Prod.{0, 0} ENNReal ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (Prod.fst.{0, 0} ENNReal ENNReal p) (Prod.snd.{0, 0} ENNReal ENNReal p)) (nhds.{0} (Prod.{0, 0} ENNReal ENNReal) (Prod.topologicalSpace.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace) (Prod.mk.{0, 0} ENNReal ENNReal a b)) (nhds.{0} ENNReal ENNReal.topologicalSpace (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a b)))
but is expected to have type
  forall {a : ENNReal} {b : ENNReal}, (Or (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Or (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Filter.Tendsto.{0, 0} (Prod.{0, 0} ENNReal ENNReal) ENNReal (fun (p : Prod.{0, 0} ENNReal ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Prod.fst.{0, 0} ENNReal ENNReal p) (Prod.snd.{0, 0} ENNReal ENNReal p)) (nhds.{0} (Prod.{0, 0} ENNReal ENNReal) (instTopologicalSpaceProd.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal) (Prod.mk.{0, 0} ENNReal ENNReal a b)) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_mul ENNReal.tendsto_mulₓ'. -/
protected theorem tendsto_mul (ha : a ≠ 0 ∨ b ≠ ⊤) (hb : b ≠ 0 ∨ a ≠ ⊤) :
    Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) :=
  by
  have ht :
    ∀ b : ℝ≥0∞, b ≠ 0 → Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) (𝓝 ((⊤ : ℝ≥0∞), b)) (𝓝 ⊤) :=
    by
    refine' fun b hb => tendsto_nhds_top_iff_nnreal.2 fun n => _
    rcases lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hb) with ⟨ε, hε, hεb⟩
    have : ∀ᶠ c : ℝ≥0∞ × ℝ≥0∞ in 𝓝 (∞, b), ↑n / ↑ε < c.1 ∧ ↑ε < c.2 :=
      (lt_mem_nhds <| div_lt_top coe_ne_top hε.ne').prod_nhds (lt_mem_nhds hεb)
    refine' this.mono fun c hc => _
    exact (ENNReal.div_mul_cancel hε.ne' coe_ne_top).symm.trans_lt (mul_lt_mul hc.1 hc.2)
  cases a
  · simp [none_eq_top] at hb
    simp [none_eq_top, ht b hb, top_mul, hb]
  cases b
  · simp [none_eq_top] at ha
    simp [*, nhds_swap (a : ℝ≥0∞) ⊤, none_eq_top, some_eq_coe, top_mul, tendsto_map'_iff, (· ∘ ·),
      mul_comm]
  simp [some_eq_coe, nhds_coe_coe, tendsto_map'_iff, (· ∘ ·)]
  simp only [coe_mul.symm, tendsto_coe, tendsto_mul]
#align ennreal.tendsto_mul ENNReal.tendsto_mul

/- warning: ennreal.tendsto.mul -> ENNReal.Tendsto.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {ma : α -> ENNReal} {mb : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal ma f (nhds.{0} ENNReal ENNReal.topologicalSpace a)) -> (Or (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Filter.Tendsto.{u1, 0} α ENNReal mb f (nhds.{0} ENNReal ENNReal.topologicalSpace b)) -> (Or (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (ma a) (mb a)) f (nhds.{0} ENNReal ENNReal.topologicalSpace (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {ma : α -> ENNReal} {mb : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal ma f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a)) -> (Or (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Filter.Tendsto.{u1, 0} α ENNReal mb f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal b)) -> (Or (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ma a) (mb a)) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto.mul ENNReal.Tendsto.mulₓ'. -/
protected theorem Tendsto.mul {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ⊤) (hmb : Tendsto mb f (𝓝 b))
    (hb : b ≠ 0 ∨ a ≠ ⊤) : Tendsto (fun a => ma a * mb a) f (𝓝 (a * b)) :=
  show Tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a * b)) from
    Tendsto.comp (ENNReal.tendsto_mul ha hb) (hma.prod_mk_nhds hmb)
#align ennreal.tendsto.mul ENNReal.Tendsto.mul

/- warning: continuous_on.ennreal_mul -> ContinuousOn.ennreal_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> ENNReal} {g : α -> ENNReal} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace f s) -> (ContinuousOn.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace g s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Or (Ne.{1} ENNReal (f x) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal (g x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Or (Ne.{1} ENNReal (g x) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal (f x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) -> (ContinuousOn.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> ENNReal} {g : α -> ENNReal} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal f s) -> (ContinuousOn.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal g s) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Or (Ne.{1} ENNReal (f x) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal (g x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Or (Ne.{1} ENNReal (g x) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal (f x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) -> (ContinuousOn.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.ennreal_mul ContinuousOn.ennreal_mulₓ'. -/
theorem ContinuousOn.ennreal_mul [TopologicalSpace α] {f g : α → ℝ≥0∞} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₁ : ∀ x ∈ s, f x ≠ 0 ∨ g x ≠ ∞)
    (h₂ : ∀ x ∈ s, g x ≠ 0 ∨ f x ≠ ∞) : ContinuousOn (fun x => f x * g x) s := fun x hx =>
  ENNReal.Tendsto.mul (hf x hx) (h₁ x hx) (hg x hx) (h₂ x hx)
#align continuous_on.ennreal_mul ContinuousOn.ennreal_mul

/- warning: continuous.ennreal_mul -> Continuous.ennreal_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> ENNReal} {g : α -> ENNReal}, (Continuous.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace f) -> (Continuous.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace g) -> (forall (x : α), Or (Ne.{1} ENNReal (f x) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal (g x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (forall (x : α), Or (Ne.{1} ENNReal (g x) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal (f x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Continuous.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> ENNReal} {g : α -> ENNReal}, (Continuous.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal f) -> (Continuous.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal g) -> (forall (x : α), Or (Ne.{1} ENNReal (f x) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal (g x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (forall (x : α), Or (Ne.{1} ENNReal (g x) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal (f x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Continuous.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align continuous.ennreal_mul Continuous.ennreal_mulₓ'. -/
theorem Continuous.ennreal_mul [TopologicalSpace α] {f g : α → ℝ≥0∞} (hf : Continuous f)
    (hg : Continuous g) (h₁ : ∀ x, f x ≠ 0 ∨ g x ≠ ∞) (h₂ : ∀ x, g x ≠ 0 ∨ f x ≠ ∞) :
    Continuous fun x => f x * g x :=
  continuous_iff_continuousAt.2 fun x =>
    ENNReal.Tendsto.mul hf.ContinuousAt (h₁ x) hg.ContinuousAt (h₂ x)
#align continuous.ennreal_mul Continuous.ennreal_mul

/- warning: ennreal.tendsto.const_mul -> ENNReal.Tendsto.const_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.topologicalSpace b)) -> (Or (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (b : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (m b)) f (nhds.{0} ENNReal ENNReal.topologicalSpace (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal b)) -> (Or (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (b : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (m b)) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto.const_mul ENNReal.Tendsto.const_mulₓ'. -/
protected theorem Tendsto.const_mul {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b ≠ 0 ∨ a ≠ ⊤) : Tendsto (fun b => a * m b) f (𝓝 (a * b)) :=
  by_cases (fun this : a = 0 => by simp [this, tendsto_const_nhds]) fun ha : a ≠ 0 =>
    ENNReal.Tendsto.mul tendsto_const_nhds (Or.inl ha) hm hb
#align ennreal.tendsto.const_mul ENNReal.Tendsto.const_mul

/- warning: ennreal.tendsto.mul_const -> ENNReal.Tendsto.mul_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.topologicalSpace a)) -> (Or (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (m x) b) f (nhds.{0} ENNReal ENNReal.topologicalSpace (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a)) -> (Or (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (m x) b) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto.mul_const ENNReal.Tendsto.mul_constₓ'. -/
protected theorem Tendsto.mul_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ⊤) : Tendsto (fun x => m x * b) f (𝓝 (a * b)) := by
  simpa only [mul_comm] using ENNReal.Tendsto.const_mul hm ha
#align ennreal.tendsto.mul_const ENNReal.Tendsto.mul_const

/- warning: ennreal.tendsto_finset_prod_of_ne_top -> ENNReal.tendsto_finset_prod_of_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> α -> ENNReal} {x : Filter.{u1} α} {a : ι -> ENNReal} (s : Finset.{u2} ι), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Filter.Tendsto.{u1, 0} α ENNReal (f i) x (nhds.{0} ENNReal ENNReal.topologicalSpace (a i)))) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Ne.{1} ENNReal (a i) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (b : α) => Finset.prod.{0, u2} ENNReal ι (OrderedCommMonoid.toCommMonoid.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) s (fun (c : ι) => f c b)) x (nhds.{0} ENNReal ENNReal.topologicalSpace (Finset.prod.{0, u2} ENNReal ι (OrderedCommMonoid.toCommMonoid.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) s (fun (c : ι) => a c))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> α -> ENNReal} {x : Filter.{u1} α} {a : ι -> ENNReal} (s : Finset.{u2} ι), (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Filter.Tendsto.{u1, 0} α ENNReal (f i) x (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (a i)))) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Ne.{1} ENNReal (a i) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (b : α) => Finset.prod.{0, u2} ENNReal ι (LinearOrderedCommMonoid.toCommMonoid.{0} ENNReal (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{0} ENNReal ENNReal.instLinearOrderedCommMonoidWithZeroENNReal)) s (fun (c : ι) => f c b)) x (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Finset.prod.{0, u2} ENNReal ι (LinearOrderedCommMonoid.toCommMonoid.{0} ENNReal (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{0} ENNReal ENNReal.instLinearOrderedCommMonoidWithZeroENNReal)) s (fun (c : ι) => a c))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_finset_prod_of_ne_top ENNReal.tendsto_finset_prod_of_ne_topₓ'. -/
theorem tendsto_finset_prod_of_ne_top {ι : Type _} {f : ι → α → ℝ≥0∞} {x : Filter α} {a : ι → ℝ≥0∞}
    (s : Finset ι) (h : ∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) (h' : ∀ i ∈ s, a i ≠ ∞) :
    Tendsto (fun b => ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
  by
  induction' s using Finset.induction with a s has IH; · simp [tendsto_const_nhds]
  simp only [Finset.prod_insert has]
  apply tendsto.mul (h _ (Finset.mem_insert_self _ _))
  · right
    exact (prod_lt_top fun i hi => h' _ (Finset.mem_insert_of_mem hi)).Ne
  ·
    exact
      IH (fun i hi => h _ (Finset.mem_insert_of_mem hi)) fun i hi =>
        h' _ (Finset.mem_insert_of_mem hi)
  · exact Or.inr (h' _ (Finset.mem_insert_self _ _))
#align ennreal.tendsto_finset_prod_of_ne_top ENNReal.tendsto_finset_prod_of_ne_top

/- warning: ennreal.continuous_at_const_mul -> ENNReal.continuousAt_const_mul is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {b : ENNReal}, (Or (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) -> (ContinuousAt.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a) b)
but is expected to have type
  forall {a : ENNReal} {b : ENNReal}, (Or (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) -> (ContinuousAt.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal ((fun (x._@.Mathlib.Topology.Instances.ENNReal._hyg.7692 : ENNReal) (x._@.Mathlib.Topology.Instances.ENNReal._hyg.7694 : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) x._@.Mathlib.Topology.Instances.ENNReal._hyg.7692 x._@.Mathlib.Topology.Instances.ENNReal._hyg.7694) a) b)
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_at_const_mul ENNReal.continuousAt_const_mulₓ'. -/
protected theorem continuousAt_const_mul {a b : ℝ≥0∞} (h : a ≠ ⊤ ∨ b ≠ 0) :
    ContinuousAt ((· * ·) a) b :=
  Tendsto.const_mul tendsto_id h.symm
#align ennreal.continuous_at_const_mul ENNReal.continuousAt_const_mul

/- warning: ennreal.continuous_at_mul_const -> ENNReal.continuousAt_mul_const is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {b : ENNReal}, (Or (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) -> (ContinuousAt.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace (fun (x : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x a) b)
but is expected to have type
  forall {a : ENNReal} {b : ENNReal}, (Or (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) -> (ContinuousAt.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal (fun (x : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) x a) b)
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_at_mul_const ENNReal.continuousAt_mul_constₓ'. -/
protected theorem continuousAt_mul_const {a b : ℝ≥0∞} (h : a ≠ ⊤ ∨ b ≠ 0) :
    ContinuousAt (fun x => x * a) b :=
  Tendsto.mul_const tendsto_id h.symm
#align ennreal.continuous_at_mul_const ENNReal.continuousAt_mul_const

/- warning: ennreal.continuous_const_mul -> ENNReal.continuous_const_mul is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Continuous.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a))
but is expected to have type
  forall {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Continuous.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal ((fun (x._@.Mathlib.Topology.Instances.ENNReal._hyg.7858 : ENNReal) (x._@.Mathlib.Topology.Instances.ENNReal._hyg.7860 : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) x._@.Mathlib.Topology.Instances.ENNReal._hyg.7858 x._@.Mathlib.Topology.Instances.ENNReal._hyg.7860) a))
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_const_mul ENNReal.continuous_const_mulₓ'. -/
protected theorem continuous_const_mul {a : ℝ≥0∞} (ha : a ≠ ⊤) : Continuous ((· * ·) a) :=
  continuous_iff_continuousAt.2 fun x => ENNReal.continuousAt_const_mul (Or.inl ha)
#align ennreal.continuous_const_mul ENNReal.continuous_const_mul

/- warning: ennreal.continuous_mul_const -> ENNReal.continuous_mul_const is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Continuous.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace (fun (x : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x a))
but is expected to have type
  forall {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Continuous.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal (fun (x : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) x a))
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_mul_const ENNReal.continuous_mul_constₓ'. -/
protected theorem continuous_mul_const {a : ℝ≥0∞} (ha : a ≠ ⊤) : Continuous fun x => x * a :=
  continuous_iff_continuousAt.2 fun x => ENNReal.continuousAt_mul_const (Or.inl ha)
#align ennreal.continuous_mul_const ENNReal.continuous_mul_const

/- warning: ennreal.continuous_div_const -> ENNReal.continuous_div_const is a dubious translation:
lean 3 declaration is
  forall (c : ENNReal), (Ne.{1} ENNReal c (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Continuous.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace (fun (x : ENNReal) => HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) x c))
but is expected to have type
  forall (c : ENNReal), (Ne.{1} ENNReal c (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Continuous.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal (fun (x : ENNReal) => HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) x c))
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_div_const ENNReal.continuous_div_constₓ'. -/
protected theorem continuous_div_const (c : ℝ≥0∞) (c_ne_zero : c ≠ 0) :
    Continuous fun x : ℝ≥0∞ => x / c :=
  by
  simp_rw [div_eq_mul_inv, continuous_iff_continuousAt]
  intro x
  exact ENNReal.continuousAt_mul_const (Or.intro_left _ (inv_ne_top.mpr c_ne_zero))
#align ennreal.continuous_div_const ENNReal.continuous_div_const

/- warning: ennreal.continuous_pow -> ENNReal.continuous_pow is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Continuous.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace (fun (a : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) a n)
but is expected to have type
  forall (n : Nat), Continuous.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal (fun (a : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))) a n)
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_pow ENNReal.continuous_powₓ'. -/
@[continuity]
theorem continuous_pow (n : ℕ) : Continuous fun a : ℝ≥0∞ => a ^ n :=
  by
  induction' n with n IH
  · simp [continuous_const]
  simp_rw [Nat.succ_eq_add_one, pow_add, pow_one, continuous_iff_continuousAt]
  intro x
  refine' ENNReal.Tendsto.mul (IH.tendsto _) _ tendsto_id _ <;> by_cases H : x = 0
  · simp only [H, zero_ne_top, Ne.def, or_true_iff, not_false_iff]
  · exact Or.inl fun h => H (pow_eq_zero h)
  ·
    simp only [H, pow_eq_top_iff, zero_ne_top, false_or_iff, eq_self_iff_true, not_true, Ne.def,
      not_false_iff, false_and_iff]
  · simp only [H, true_or_iff, Ne.def, not_false_iff]
#align ennreal.continuous_pow ENNReal.continuous_pow

/- warning: ennreal.continuous_on_sub -> ENNReal.continuousOn_sub is a dubious translation:
lean 3 declaration is
  ContinuousOn.{0, 0} (Prod.{0, 0} ENNReal ENNReal) ENNReal (Prod.topologicalSpace.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace) ENNReal.topologicalSpace (fun (p : Prod.{0, 0} ENNReal ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (Prod.fst.{0, 0} ENNReal ENNReal p) (Prod.snd.{0, 0} ENNReal ENNReal p)) (setOf.{0} (Prod.{0, 0} ENNReal ENNReal) (fun (p : Prod.{0, 0} ENNReal ENNReal) => Ne.{1} (Prod.{0, 0} ENNReal ENNReal) p (Prod.mk.{0, 0} ENNReal ENNReal (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))))
but is expected to have type
  ContinuousOn.{0, 0} (Prod.{0, 0} ENNReal ENNReal) ENNReal (instTopologicalSpaceProd.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal) ENNReal.instTopologicalSpaceENNReal (fun (p : Prod.{0, 0} ENNReal ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (Prod.fst.{0, 0} ENNReal ENNReal p) (Prod.snd.{0, 0} ENNReal ENNReal p)) (setOf.{0} (Prod.{0, 0} ENNReal ENNReal) (fun (p : Prod.{0, 0} ENNReal ENNReal) => Ne.{1} (Prod.{0, 0} ENNReal ENNReal) p (Prod.mk.{0, 0} ENNReal ENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))))
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_on_sub ENNReal.continuousOn_subₓ'. -/
theorem continuousOn_sub :
    ContinuousOn (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) { p : ℝ≥0∞ × ℝ≥0∞ | p ≠ ⟨∞, ∞⟩ } :=
  by
  rw [ContinuousOn]
  rintro ⟨x, y⟩ hp
  simp only [Ne.def, Set.mem_setOf_eq, Prod.mk.inj_iff] at hp
  refine' tendsto_nhdsWithin_of_tendsto_nhds (tendsto_sub (not_and_distrib.mp hp))
#align ennreal.continuous_on_sub ENNReal.continuousOn_sub

/- warning: ennreal.continuous_sub_left -> ENNReal.continuous_sub_left is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Continuous.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace (fun (x : ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) a x))
but is expected to have type
  forall {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Continuous.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal (fun (x : ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) a x))
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_sub_left ENNReal.continuous_sub_leftₓ'. -/
theorem continuous_sub_left {a : ℝ≥0∞} (a_ne_top : a ≠ ⊤) : Continuous fun x => a - x :=
  by
  rw [show (fun x => a - x) = (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) ∘ fun x => ⟨a, x⟩ by rfl]
  apply ContinuousOn.comp_continuous continuous_on_sub (Continuous.Prod.mk a)
  intro x
  simp only [a_ne_top, Ne.def, mem_set_of_eq, Prod.mk.inj_iff, false_and_iff, not_false_iff]
#align ennreal.continuous_sub_left ENNReal.continuous_sub_left

/- warning: ennreal.continuous_nnreal_sub -> ENNReal.continuous_nnreal_sub is a dubious translation:
lean 3 declaration is
  forall {a : NNReal}, Continuous.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace (fun (x : ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) a) x)
but is expected to have type
  forall {a : NNReal}, Continuous.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal (fun (x : ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (ENNReal.some a) x)
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_nnreal_sub ENNReal.continuous_nnreal_subₓ'. -/
theorem continuous_nnreal_sub {a : ℝ≥0} : Continuous fun x : ℝ≥0∞ => (a : ℝ≥0∞) - x :=
  continuous_sub_left coe_ne_top
#align ennreal.continuous_nnreal_sub ENNReal.continuous_nnreal_sub

/- warning: ennreal.continuous_on_sub_left -> ENNReal.continuousOn_sub_left is a dubious translation:
lean 3 declaration is
  forall (a : ENNReal), ContinuousOn.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace (fun (x : ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) a x) (setOf.{0} ENNReal (fun (x : ENNReal) => Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall (a : ENNReal), ContinuousOn.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal (fun (x : ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) a x) (setOf.{0} ENNReal (fun (x : ENNReal) => Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_on_sub_left ENNReal.continuousOn_sub_leftₓ'. -/
theorem continuousOn_sub_left (a : ℝ≥0∞) : ContinuousOn (fun x => a - x) { x : ℝ≥0∞ | x ≠ ∞ } :=
  by
  rw [show (fun x => a - x) = (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) ∘ fun x => ⟨a, x⟩ by rfl]
  apply ContinuousOn.comp continuous_on_sub (Continuous.continuousOn (Continuous.Prod.mk a))
  rintro _ h (_ | _)
  exact h none_eq_top
#align ennreal.continuous_on_sub_left ENNReal.continuousOn_sub_left

/- warning: ennreal.continuous_sub_right -> ENNReal.continuous_sub_right is a dubious translation:
lean 3 declaration is
  forall (a : ENNReal), Continuous.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace (fun (x : ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) x a)
but is expected to have type
  forall (a : ENNReal), Continuous.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal (fun (x : ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) x a)
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_sub_right ENNReal.continuous_sub_rightₓ'. -/
theorem continuous_sub_right (a : ℝ≥0∞) : Continuous fun x : ℝ≥0∞ => x - a :=
  by
  by_cases a_infty : a = ∞
  · simp [a_infty, continuous_const]
  · rw [show (fun x => x - a) = (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) ∘ fun x => ⟨x, a⟩ by rfl]
    apply ContinuousOn.comp_continuous continuous_on_sub (continuous_id'.prod_mk continuous_const)
    intro x
    simp only [a_infty, Ne.def, mem_set_of_eq, Prod.mk.inj_iff, and_false_iff, not_false_iff]
#align ennreal.continuous_sub_right ENNReal.continuous_sub_right

/- warning: ennreal.tendsto.pow -> ENNReal.Tendsto.pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} {n : Nat}, (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.topologicalSpace a)) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (m x) n) f (nhds.{0} ENNReal ENNReal.topologicalSpace (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) a n)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} {n : Nat}, (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a)) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))) (m x) n) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))) a n)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto.pow ENNReal.Tendsto.powₓ'. -/
protected theorem Tendsto.pow {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} {n : ℕ}
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ n) f (𝓝 (a ^ n)) :=
  ((continuous_pow n).Tendsto a).comp hm
#align ennreal.tendsto.pow ENNReal.Tendsto.pow

/- warning: ennreal.le_of_forall_lt_one_mul_le -> ENNReal.le_of_forall_lt_one_mul_le is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal}, (forall (a : ENNReal), (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) a (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a x) y)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x y)
but is expected to have type
  forall {x : ENNReal} {y : ENNReal}, (forall (a : ENNReal), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) a (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a x) y)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x y)
Case conversion may be inaccurate. Consider using '#align ennreal.le_of_forall_lt_one_mul_le ENNReal.le_of_forall_lt_one_mul_leₓ'. -/
theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0∞} (h : ∀ a < 1, a * x ≤ y) : x ≤ y :=
  by
  have : tendsto (· * x) (𝓝[<] 1) (𝓝 (1 * x)) :=
    (ENNReal.continuousAt_mul_const (Or.inr one_ne_zero)).mono_left inf_le_left
  rw [one_mul] at this
  haveI : (𝓝[<] (1 : ℝ≥0∞)).ne_bot := nhdsWithin_Iio_self_neBot' ⟨0, zero_lt_one⟩
  exact le_of_tendsto this (eventually_nhdsWithin_iff.2 <| eventually_of_forall h)
#align ennreal.le_of_forall_lt_one_mul_le ENNReal.le_of_forall_lt_one_mul_le

/- warning: ennreal.infi_mul_left' -> ENNReal.iInf_mul_left' is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {a : ENNReal}, ((Eq.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{u1} ι (fun (i : ι) => Eq.{1} ENNReal (f i) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))) -> ((Eq.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Nonempty.{u1} ι)) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (f i))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {a : ENNReal}, ((Eq.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{u1} ι (fun (i : ι) => Eq.{1} ENNReal (f i) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))) -> ((Eq.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Nonempty.{u1} ι)) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (f i))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align ennreal.infi_mul_left' ENNReal.iInf_mul_left'ₓ'. -/
theorem iInf_mul_left' {ι} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0)
    (h0 : a = 0 → Nonempty ι) : (⨅ i, a * f i) = a * ⨅ i, f i :=
  by
  by_cases H : a = ⊤ ∧ (⨅ i, f i) = 0
  · rcases h H.1 H.2 with ⟨i, hi⟩
    rw [H.2, MulZeroClass.mul_zero, ← bot_eq_zero, iInf_eq_bot]
    exact fun b hb => ⟨i, by rwa [hi, MulZeroClass.mul_zero, ← bot_eq_zero]⟩
  · rw [not_and_or] at H
    cases isEmpty_or_nonempty ι
    · rw [iInf_of_empty, iInf_of_empty, mul_top, if_neg]
      exact mt h0 (not_nonempty_iff.2 ‹_›)
    ·
      exact
        (ennreal.mul_left_mono.map_infi_of_continuous_at' (ENNReal.continuousAt_const_mul H)).symm
#align ennreal.infi_mul_left' ENNReal.iInf_mul_left'

/- warning: ennreal.infi_mul_left -> ENNReal.iInf_mul_left is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {f : ι -> ENNReal} {a : ENNReal}, ((Eq.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{u1} ι (fun (i : ι) => Eq.{1} ENNReal (f i) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (f i))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => f i))))
but is expected to have type
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {f : ι -> ENNReal} {a : ENNReal}, ((Eq.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{u1} ι (fun (i : ι) => Eq.{1} ENNReal (f i) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (f i))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align ennreal.infi_mul_left ENNReal.iInf_mul_leftₓ'. -/
theorem iInf_mul_left {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {a : ℝ≥0∞}
    (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0) : (⨅ i, a * f i) = a * ⨅ i, f i :=
  iInf_mul_left' h fun _ => ‹Nonempty ι›
#align ennreal.infi_mul_left ENNReal.iInf_mul_left

/- warning: ennreal.infi_mul_right' -> ENNReal.iInf_mul_right' is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {a : ENNReal}, ((Eq.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{u1} ι (fun (i : ι) => Eq.{1} ENNReal (f i) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))) -> ((Eq.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Nonempty.{u1} ι)) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f i) a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => f i)) a))
but is expected to have type
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {a : ENNReal}, ((Eq.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{u1} ι (fun (i : ι) => Eq.{1} ENNReal (f i) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))) -> ((Eq.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Nonempty.{u1} ι)) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f i) a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => f i)) a))
Case conversion may be inaccurate. Consider using '#align ennreal.infi_mul_right' ENNReal.iInf_mul_right'ₓ'. -/
theorem iInf_mul_right' {ι} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0)
    (h0 : a = 0 → Nonempty ι) : (⨅ i, f i * a) = (⨅ i, f i) * a := by
  simpa only [mul_comm a] using infi_mul_left' h h0
#align ennreal.infi_mul_right' ENNReal.iInf_mul_right'

/- warning: ennreal.infi_mul_right -> ENNReal.iInf_mul_right is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {f : ι -> ENNReal} {a : ENNReal}, ((Eq.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{u1} ι (fun (i : ι) => Eq.{1} ENNReal (f i) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f i) a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => f i)) a))
but is expected to have type
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {f : ι -> ENNReal} {a : ENNReal}, ((Eq.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{u1} ι (fun (i : ι) => Eq.{1} ENNReal (f i) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))) -> (Eq.{1} ENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f i) a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => f i)) a))
Case conversion may be inaccurate. Consider using '#align ennreal.infi_mul_right ENNReal.iInf_mul_rightₓ'. -/
theorem iInf_mul_right {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {a : ℝ≥0∞}
    (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0) : (⨅ i, f i * a) = (⨅ i, f i) * a :=
  iInf_mul_right' h fun _ => ‹Nonempty ι›
#align ennreal.infi_mul_right ENNReal.iInf_mul_right

/- warning: ennreal.inv_map_infi -> ENNReal.inv_map_iInf is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {x : ι -> ENNReal}, Eq.{1} ENNReal (Inv.inv.{0} ENNReal ENNReal.hasInv (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι x)) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => Inv.inv.{0} ENNReal ENNReal.hasInv (x i)))
but is expected to have type
  forall {ι : Sort.{u1}} {x : ι -> ENNReal}, Eq.{1} ENNReal (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι x)) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => Inv.inv.{0} ENNReal ENNReal.instInvENNReal (x i)))
Case conversion may be inaccurate. Consider using '#align ennreal.inv_map_infi ENNReal.inv_map_iInfₓ'. -/
theorem inv_map_iInf {ι : Sort _} {x : ι → ℝ≥0∞} : (iInf x)⁻¹ = ⨆ i, (x i)⁻¹ :=
  OrderIso.invENNReal.map_iInf x
#align ennreal.inv_map_infi ENNReal.inv_map_iInf

/- warning: ennreal.inv_map_supr -> ENNReal.inv_map_iSup is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {x : ι -> ENNReal}, Eq.{1} ENNReal (Inv.inv.{0} ENNReal ENNReal.hasInv (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι x)) (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => Inv.inv.{0} ENNReal ENNReal.hasInv (x i)))
but is expected to have type
  forall {ι : Sort.{u1}} {x : ι -> ENNReal}, Eq.{1} ENNReal (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι x)) (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => Inv.inv.{0} ENNReal ENNReal.instInvENNReal (x i)))
Case conversion may be inaccurate. Consider using '#align ennreal.inv_map_supr ENNReal.inv_map_iSupₓ'. -/
theorem inv_map_iSup {ι : Sort _} {x : ι → ℝ≥0∞} : (iSup x)⁻¹ = ⨅ i, (x i)⁻¹ :=
  OrderIso.invENNReal.map_iSup x
#align ennreal.inv_map_supr ENNReal.inv_map_iSup

/- warning: ennreal.inv_limsup -> ENNReal.inv_limsup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {x : ι -> ENNReal} {l : Filter.{u1} ι}, Eq.{1} ENNReal (Inv.inv.{0} ENNReal ENNReal.hasInv (Filter.limsup.{0, u1} ENNReal ι (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) x l)) (Filter.liminf.{0, u1} ENNReal ι (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (i : ι) => Inv.inv.{0} ENNReal ENNReal.hasInv (x i)) l)
but is expected to have type
  forall {ι : Type.{u1}} {x : ι -> ENNReal} {l : Filter.{u1} ι}, Eq.{1} ENNReal (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (Filter.limsup.{0, u1} ENNReal ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) x l)) (Filter.liminf.{0, u1} ENNReal ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (i : ι) => Inv.inv.{0} ENNReal ENNReal.instInvENNReal (x i)) l)
Case conversion may be inaccurate. Consider using '#align ennreal.inv_limsup ENNReal.inv_limsupₓ'. -/
theorem inv_limsup {ι : Sort _} {x : ι → ℝ≥0∞} {l : Filter ι} :
    (limsup x l)⁻¹ = liminf (fun i => (x i)⁻¹) l := by
  simp only [limsup_eq_infi_supr, inv_map_infi, inv_map_supr, liminf_eq_supr_infi]
#align ennreal.inv_limsup ENNReal.inv_limsup

/- warning: ennreal.inv_liminf -> ENNReal.inv_liminf is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {x : ι -> ENNReal} {l : Filter.{u1} ι}, Eq.{1} ENNReal (Inv.inv.{0} ENNReal ENNReal.hasInv (Filter.liminf.{0, u1} ENNReal ι (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) x l)) (Filter.limsup.{0, u1} ENNReal ι (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (i : ι) => Inv.inv.{0} ENNReal ENNReal.hasInv (x i)) l)
but is expected to have type
  forall {ι : Type.{u1}} {x : ι -> ENNReal} {l : Filter.{u1} ι}, Eq.{1} ENNReal (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (Filter.liminf.{0, u1} ENNReal ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) x l)) (Filter.limsup.{0, u1} ENNReal ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (i : ι) => Inv.inv.{0} ENNReal ENNReal.instInvENNReal (x i)) l)
Case conversion may be inaccurate. Consider using '#align ennreal.inv_liminf ENNReal.inv_liminfₓ'. -/
theorem inv_liminf {ι : Sort _} {x : ι → ℝ≥0∞} {l : Filter ι} :
    (liminf x l)⁻¹ = limsup (fun i => (x i)⁻¹) l := by
  simp only [limsup_eq_infi_supr, inv_map_infi, inv_map_supr, liminf_eq_supr_infi]
#align ennreal.inv_liminf ENNReal.inv_liminf

instance : ContinuousInv ℝ≥0∞ :=
  ⟨OrderIso.invENNReal.Continuous⟩

/- warning: ennreal.tendsto_inv_iff -> ENNReal.tendsto_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal}, Iff (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => Inv.inv.{0} ENNReal ENNReal.hasInv (m x)) f (nhds.{0} ENNReal ENNReal.topologicalSpace (Inv.inv.{0} ENNReal ENNReal.hasInv a))) (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.topologicalSpace a))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal}, Iff (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => Inv.inv.{0} ENNReal ENNReal.instInvENNReal (m x)) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Inv.inv.{0} ENNReal ENNReal.instInvENNReal a))) (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_inv_iff ENNReal.tendsto_inv_iffₓ'. -/
@[simp]
protected theorem tendsto_inv_iff {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
    Tendsto (fun x => (m x)⁻¹) f (𝓝 a⁻¹) ↔ Tendsto m f (𝓝 a) :=
  ⟨fun h => by simpa only [inv_inv] using tendsto.inv h, Tendsto.inv⟩
#align ennreal.tendsto_inv_iff ENNReal.tendsto_inv_iff

/- warning: ennreal.tendsto.div -> ENNReal.Tendsto.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {ma : α -> ENNReal} {mb : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal ma f (nhds.{0} ENNReal ENNReal.topologicalSpace a)) -> (Or (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) -> (Filter.Tendsto.{u1, 0} α ENNReal mb f (nhds.{0} ENNReal ENNReal.topologicalSpace b)) -> (Or (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (a : α) => HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) (ma a) (mb a)) f (nhds.{0} ENNReal ENNReal.topologicalSpace (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) a b)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {ma : α -> ENNReal} {mb : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal ma f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a)) -> (Or (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) -> (Filter.Tendsto.{u1, 0} α ENNReal mb f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal b)) -> (Or (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (a : α) => HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) (ma a) (mb a)) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto.div ENNReal.Tendsto.divₓ'. -/
protected theorem Tendsto.div {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) (hmb : Tendsto mb f (𝓝 b))
    (hb : b ≠ ⊤ ∨ a ≠ ⊤) : Tendsto (fun a => ma a / mb a) f (𝓝 (a / b)) := by
  apply tendsto.mul hma _ (ENNReal.tendsto_inv_iff.2 hmb) _ <;> simp [ha, hb]
#align ennreal.tendsto.div ENNReal.Tendsto.div

/- warning: ennreal.tendsto.const_div -> ENNReal.Tendsto.const_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.topologicalSpace b)) -> (Or (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (b : α) => HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) a (m b)) f (nhds.{0} ENNReal ENNReal.topologicalSpace (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) a b)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal b)) -> (Or (Ne.{1} ENNReal b (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Ne.{1} ENNReal a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (b : α) => HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) a (m b)) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto.const_div ENNReal.Tendsto.const_divₓ'. -/
protected theorem Tendsto.const_div {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b ≠ ⊤ ∨ a ≠ ⊤) : Tendsto (fun b => a / m b) f (𝓝 (a / b)) :=
  by
  apply tendsto.const_mul (ENNReal.tendsto_inv_iff.2 hm)
  simp [hb]
#align ennreal.tendsto.const_div ENNReal.Tendsto.const_div

/- warning: ennreal.tendsto.div_const -> ENNReal.Tendsto.div_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.topologicalSpace a)) -> (Or (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) (m x) b) f (nhds.{0} ENNReal ENNReal.topologicalSpace (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) a b)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} {b : ENNReal}, (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a)) -> (Or (Ne.{1} ENNReal a (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal b (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) (m x) b) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto.div_const ENNReal.Tendsto.div_constₓ'. -/
protected theorem Tendsto.div_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) : Tendsto (fun x => m x / b) f (𝓝 (a / b)) :=
  by
  apply tendsto.mul_const hm
  simp [ha]
#align ennreal.tendsto.div_const ENNReal.Tendsto.div_const

/- warning: ennreal.tendsto_inv_nat_nhds_zero -> ENNReal.tendsto_inv_nat_nhds_zero is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => Inv.inv.{0} ENNReal ENNReal.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENNReal (HasLiftT.mk.{1, 1} Nat ENNReal (CoeTCₓ.coe.{1, 1} Nat ENNReal (Nat.castCoe.{0} ENNReal (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => Inv.inv.{0} ENNReal ENNReal.instInvENNReal (Nat.cast.{0} ENNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_inv_nat_nhds_zero ENNReal.tendsto_inv_nat_nhds_zeroₓ'. -/
protected theorem tendsto_inv_nat_nhds_zero : Tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
  ENNReal.inv_top ▸ ENNReal.tendsto_inv_iff.2 tendsto_nat_nhds_top
#align ennreal.tendsto_inv_nat_nhds_zero ENNReal.tendsto_inv_nat_nhds_zero

/- warning: ennreal.supr_add -> ENNReal.iSup_add is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {ι : Sort.{u1}} {s : ι -> ENNReal} [h : Nonempty.{u1} ι], Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι s) a) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (b : ι) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (s b) a))
but is expected to have type
  forall {a : ENNReal} {ι : Sort.{u1}} {s : ι -> ENNReal} [h : Nonempty.{u1} ι], Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι s) a) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (b : ι) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (s b) a))
Case conversion may be inaccurate. Consider using '#align ennreal.supr_add ENNReal.iSup_addₓ'. -/
theorem iSup_add {ι : Sort _} {s : ι → ℝ≥0∞} [h : Nonempty ι] : iSup s + a = ⨆ b, s b + a :=
  Monotone.map_iSup_of_continuousAt' (continuousAt_id.add continuousAt_const) <|
    monotone_id.add monotone_const
#align ennreal.supr_add ENNReal.iSup_add

/- warning: ennreal.bsupr_add' -> ENNReal.biSup_add' is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {ι : Sort.{u1}} {p : ι -> Prop}, (Exists.{u1} ι (fun (i : ι) => p i)) -> (forall {f : ι -> ENNReal}, Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (p i) (fun (hi : p i) => f i))) a) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (p i) (fun (hi : p i) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f i) a))))
but is expected to have type
  forall {a : ENNReal} {ι : Sort.{u1}} {p : ι -> Prop}, (Exists.{u1} ι (fun (i : ι) => p i)) -> (forall {f : ι -> ENNReal}, Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (p i) (fun (hi : p i) => f i))) a) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (p i) (fun (hi : p i) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f i) a))))
Case conversion may be inaccurate. Consider using '#align ennreal.bsupr_add' ENNReal.biSup_add'ₓ'. -/
theorem biSup_add' {ι : Sort _} {p : ι → Prop} (h : ∃ i, p i) {f : ι → ℝ≥0∞} :
    (⨆ (i) (hi : p i), f i) + a = ⨆ (i) (hi : p i), f i + a :=
  by
  haveI : Nonempty { i // p i } := nonempty_subtype.2 h
  simp only [iSup_subtype', supr_add]
#align ennreal.bsupr_add' ENNReal.biSup_add'

/- warning: ennreal.add_bsupr' -> ENNReal.add_biSup' is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {ι : Sort.{u1}} {p : ι -> Prop}, (Exists.{u1} ι (fun (i : ι) => p i)) -> (forall {f : ι -> ENNReal}, Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (p i) (fun (hi : p i) => f i)))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (p i) (fun (hi : p i) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (f i)))))
but is expected to have type
  forall {a : ENNReal} {ι : Sort.{u1}} {p : ι -> Prop}, (Exists.{u1} ι (fun (i : ι) => p i)) -> (forall {f : ι -> ENNReal}, Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) a (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (p i) (fun (hi : p i) => f i)))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (p i) (fun (hi : p i) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) a (f i)))))
Case conversion may be inaccurate. Consider using '#align ennreal.add_bsupr' ENNReal.add_biSup'ₓ'. -/
theorem add_biSup' {ι : Sort _} {p : ι → Prop} (h : ∃ i, p i) {f : ι → ℝ≥0∞} :
    (a + ⨆ (i) (hi : p i), f i) = ⨆ (i) (hi : p i), a + f i := by
  simp only [add_comm a, bsupr_add' h]
#align ennreal.add_bsupr' ENNReal.add_biSup'

/- warning: ennreal.bsupr_add -> ENNReal.biSup_add is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {ι : Type.{u1}} {s : Set.{u1} ι}, (Set.Nonempty.{u1} ι s) -> (forall {f : ι -> ENNReal}, Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => f i))) a) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f i) a))))
but is expected to have type
  forall {a : ENNReal} {ι : Type.{u1}} {s : Set.{u1} ι}, (Set.Nonempty.{u1} ι s) -> (forall {f : ι -> ENNReal}, Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) => f i))) a) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f i) a))))
Case conversion may be inaccurate. Consider using '#align ennreal.bsupr_add ENNReal.biSup_addₓ'. -/
theorem biSup_add {ι} {s : Set ι} (hs : s.Nonempty) {f : ι → ℝ≥0∞} :
    (⨆ i ∈ s, f i) + a = ⨆ i ∈ s, f i + a :=
  biSup_add' hs
#align ennreal.bsupr_add ENNReal.biSup_add

/- warning: ennreal.add_bsupr -> ENNReal.add_biSup is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {ι : Type.{u1}} {s : Set.{u1} ι}, (Set.Nonempty.{u1} ι s) -> (forall {f : ι -> ENNReal}, Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => f i)))) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (f i)))))
but is expected to have type
  forall {a : ENNReal} {ι : Type.{u1}} {s : Set.{u1} ι}, (Set.Nonempty.{u1} ι s) -> (forall {f : ι -> ENNReal}, Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) a (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) => f i)))) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) a (f i)))))
Case conversion may be inaccurate. Consider using '#align ennreal.add_bsupr ENNReal.add_biSupₓ'. -/
theorem add_biSup {ι} {s : Set ι} (hs : s.Nonempty) {f : ι → ℝ≥0∞} :
    (a + ⨆ i ∈ s, f i) = ⨆ i ∈ s, a + f i :=
  add_biSup' hs
#align ennreal.add_bsupr ENNReal.add_biSup

/- warning: ennreal.Sup_add -> ENNReal.sSup_add is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {s : Set.{0} ENNReal}, (Set.Nonempty.{0} ENNReal s) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (SupSet.sSup.{0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) s) a) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ENNReal (fun (b : ENNReal) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) b s) (fun (H : Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) b s) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) b a))))
but is expected to have type
  forall {a : ENNReal} {s : Set.{0} ENNReal}, (Set.Nonempty.{0} ENNReal s) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (SupSet.sSup.{0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) s) a) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ENNReal (fun (b : ENNReal) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) b s) (fun (H : Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) b s) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) b a))))
Case conversion may be inaccurate. Consider using '#align ennreal.Sup_add ENNReal.sSup_addₓ'. -/
theorem sSup_add {s : Set ℝ≥0∞} (hs : s.Nonempty) : sSup s + a = ⨆ b ∈ s, b + a := by
  rw [sSup_eq_iSup, bsupr_add hs]
#align ennreal.Sup_add ENNReal.sSup_add

/- warning: ennreal.add_supr -> ENNReal.add_iSup is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {ι : Sort.{u1}} {s : ι -> ENNReal} [_inst_1 : Nonempty.{u1} ι], Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι s)) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (b : ι) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (s b)))
but is expected to have type
  forall {a : ENNReal} {ι : Sort.{u1}} {s : ι -> ENNReal} [_inst_1 : Nonempty.{u1} ι], Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) a (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι s)) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (b : ι) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) a (s b)))
Case conversion may be inaccurate. Consider using '#align ennreal.add_supr ENNReal.add_iSupₓ'. -/
theorem add_iSup {ι : Sort _} {s : ι → ℝ≥0∞} [Nonempty ι] : a + iSup s = ⨆ b, a + s b := by
  rw [add_comm, supr_add] <;> simp [add_comm]
#align ennreal.add_supr ENNReal.add_iSup

/- warning: ennreal.supr_add_supr_le -> ENNReal.iSup_add_iSup_le is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {ι' : Sort.{u2}} [_inst_1 : Nonempty.{u1} ι] [_inst_2 : Nonempty.{u2} ι'] {f : ι -> ENNReal} {g : ι' -> ENNReal} {a : ENNReal}, (forall (i : ι) (j : ι'), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f i) (g j)) a) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι f) (iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι' g)) a)
but is expected to have type
  forall {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : Nonempty.{u2} ι] [_inst_2 : Nonempty.{u1} ι'] {f : ι -> ENNReal} {g : ι' -> ENNReal} {a : ENNReal}, (forall (i : ι) (j : ι'), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f i) (g j)) a) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι f) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι' g)) a)
Case conversion may be inaccurate. Consider using '#align ennreal.supr_add_supr_le ENNReal.iSup_add_iSup_leₓ'. -/
theorem iSup_add_iSup_le {ι ι' : Sort _} [Nonempty ι] [Nonempty ι'] {f : ι → ℝ≥0∞} {g : ι' → ℝ≥0∞}
    {a : ℝ≥0∞} (h : ∀ i j, f i + g j ≤ a) : iSup f + iSup g ≤ a := by
  simpa only [add_supr, supr_add] using iSup₂_le h
#align ennreal.supr_add_supr_le ENNReal.iSup_add_iSup_le

/- warning: ennreal.bsupr_add_bsupr_le' -> ENNReal.biSup_add_biSup_le' is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {ι' : Sort.{u2}} {p : ι -> Prop} {q : ι' -> Prop}, (Exists.{u1} ι (fun (i : ι) => p i)) -> (Exists.{u2} ι' (fun (j : ι') => q j)) -> (forall {f : ι -> ENNReal} {g : ι' -> ENNReal} {a : ENNReal}, (forall (i : ι), (p i) -> (forall (j : ι'), (q j) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f i) (g j)) a))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (p i) (fun (hi : p i) => f i))) (iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι' (fun (j : ι') => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (q j) (fun (hj : q j) => g j)))) a))
but is expected to have type
  forall {ι : Sort.{u2}} {ι' : Sort.{u1}} {p : ι -> Prop} {q : ι' -> Prop}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Exists.{u1} ι' (fun (j : ι') => q j)) -> (forall {f : ι -> ENNReal} {g : ι' -> ENNReal} {a : ENNReal}, (forall (i : ι), (p i) -> (forall (j : ι'), (q j) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f i) (g j)) a))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (p i) (fun (hi : p i) => f i))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι' (fun (j : ι') => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (q j) (fun (hj : q j) => g j)))) a))
Case conversion may be inaccurate. Consider using '#align ennreal.bsupr_add_bsupr_le' ENNReal.biSup_add_biSup_le'ₓ'. -/
theorem biSup_add_biSup_le' {ι ι'} {p : ι → Prop} {q : ι' → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {f : ι → ℝ≥0∞} {g : ι' → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ (i) (hi : p i) (j) (hj : q j), f i + g j ≤ a) :
    ((⨆ (i) (hi : p i), f i) + ⨆ (j) (hj : q j), g j) ≤ a :=
  by
  simp_rw [bsupr_add' hp, add_bsupr' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)
#align ennreal.bsupr_add_bsupr_le' ENNReal.biSup_add_biSup_le'

/- warning: ennreal.bsupr_add_bsupr_le -> ENNReal.biSup_add_biSup_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {s : Set.{u1} ι} {t : Set.{u2} ι'}, (Set.Nonempty.{u1} ι s) -> (Set.Nonempty.{u2} ι' t) -> (forall {f : ι -> ENNReal} {g : ι' -> ENNReal} {a : ENNReal}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (forall (j : ι'), (Membership.Mem.{u2, u2} ι' (Set.{u2} ι') (Set.hasMem.{u2} ι') j t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f i) (g j)) a))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => f i))) (iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι' (fun (j : ι') => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u2, u2} ι' (Set.{u2} ι') (Set.hasMem.{u2} ι') j t) (fun (H : Membership.Mem.{u2, u2} ι' (Set.{u2} ι') (Set.hasMem.{u2} ι') j t) => g j)))) a))
but is expected to have type
  forall {ι : Type.{u2}} {ι' : Type.{u1}} {s : Set.{u2} ι} {t : Set.{u1} ι'}, (Set.Nonempty.{u2} ι s) -> (Set.Nonempty.{u1} ι' t) -> (forall {f : ι -> ENNReal} {g : ι' -> ENNReal} {a : ENNReal}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (forall (j : ι'), (Membership.mem.{u1, u1} ι' (Set.{u1} ι') (Set.instMembershipSet.{u1} ι') j t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f i) (g j)) a))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι' (fun (j : ι') => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} ι' (Set.{u1} ι') (Set.instMembershipSet.{u1} ι') j t) (fun (H : Membership.mem.{u1, u1} ι' (Set.{u1} ι') (Set.instMembershipSet.{u1} ι') j t) => g j)))) a))
Case conversion may be inaccurate. Consider using '#align ennreal.bsupr_add_bsupr_le ENNReal.biSup_add_biSup_leₓ'. -/
theorem biSup_add_biSup_le {ι ι'} {s : Set ι} {t : Set ι'} (hs : s.Nonempty) (ht : t.Nonempty)
    {f : ι → ℝ≥0∞} {g : ι' → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ i ∈ s, ∀ j ∈ t, f i + g j ≤ a) :
    ((⨆ i ∈ s, f i) + ⨆ j ∈ t, g j) ≤ a :=
  biSup_add_biSup_le' hs ht h
#align ennreal.bsupr_add_bsupr_le ENNReal.biSup_add_biSup_le

/- warning: ennreal.supr_add_supr -> ENNReal.iSup_add_iSup is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {g : ι -> ENNReal}, (forall (i : ι) (j : ι), Exists.{u1} ι (fun (k : ι) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f i) (g j)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f k) (g k)))) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι f) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι g)) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (a : ι) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (g a))))
but is expected to have type
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {g : ι -> ENNReal}, (forall (i : ι) (j : ι), Exists.{u1} ι (fun (k : ι) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f i) (g j)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f k) (g k)))) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι f) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι g)) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (a : ι) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f a) (g a))))
Case conversion may be inaccurate. Consider using '#align ennreal.supr_add_supr ENNReal.iSup_add_iSupₓ'. -/
theorem iSup_add_iSup {ι : Sort _} {f g : ι → ℝ≥0∞} (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ a, f a + g a :=
  by
  cases isEmpty_or_nonempty ι
  · simp only [iSup_of_empty, bot_eq_zero, zero_add]
  · refine' le_antisymm _ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine' supr_add_supr_le fun i j => _
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk
#align ennreal.supr_add_supr ENNReal.iSup_add_iSup

/- warning: ennreal.supr_add_supr_of_monotone -> ENNReal.iSup_add_iSup_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} ι] {f : ι -> ENNReal} {g : ι -> ENNReal}, (Monotone.{u1, 0} ι ENNReal (PartialOrder.toPreorder.{u1} ι (SemilatticeSup.toPartialOrder.{u1} ι _inst_1)) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) f) -> (Monotone.{u1, 0} ι ENNReal (PartialOrder.toPreorder.{u1} ι (SemilatticeSup.toPartialOrder.{u1} ι _inst_1)) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) g) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι f) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι g)) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (a : ι) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (g a))))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} ι] {f : ι -> ENNReal} {g : ι -> ENNReal}, (Monotone.{u1, 0} ι ENNReal (PartialOrder.toPreorder.{u1} ι (SemilatticeSup.toPartialOrder.{u1} ι _inst_1)) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) f) -> (Monotone.{u1, 0} ι ENNReal (PartialOrder.toPreorder.{u1} ι (SemilatticeSup.toPartialOrder.{u1} ι _inst_1)) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) g) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι f) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι g)) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (a : ι) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f a) (g a))))
Case conversion may be inaccurate. Consider using '#align ennreal.supr_add_supr_of_monotone ENNReal.iSup_add_iSup_of_monotoneₓ'. -/
theorem iSup_add_iSup_of_monotone {ι : Sort _} [SemilatticeSup ι] {f g : ι → ℝ≥0∞} (hf : Monotone f)
    (hg : Monotone g) : iSup f + iSup g = ⨆ a, f a + g a :=
  iSup_add_iSup fun i j => ⟨i ⊔ j, add_le_add (hf <| le_sup_left) (hg <| le_sup_right)⟩
#align ennreal.supr_add_supr_of_monotone ENNReal.iSup_add_iSup_of_monotone

/- warning: ennreal.finset_sum_supr_nat -> ENNReal.finset_sum_iSup_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : SemilatticeSup.{u2} ι] {s : Finset.{u1} α} {f : α -> ι -> ENNReal}, (forall (a : α), Monotone.{u2, 0} ι ENNReal (PartialOrder.toPreorder.{u2} ι (SemilatticeSup.toPartialOrder.{u2} ι _inst_1)) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (f a)) -> (Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (a : α) => iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (f a))) (iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (n : ι) => Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (a : α) => f a n))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} ι] {s : Finset.{u2} α} {f : α -> ι -> ENNReal}, (forall (a : α), Monotone.{u1, 0} ι ENNReal (PartialOrder.toPreorder.{u1} ι (SemilatticeSup.toPartialOrder.{u1} ι _inst_1)) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (f a)) -> (Eq.{1} ENNReal (Finset.sum.{0, u2} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (a : α) => iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (f a))) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (n : ι) => Finset.sum.{0, u2} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (a : α) => f a n))))
Case conversion may be inaccurate. Consider using '#align ennreal.finset_sum_supr_nat ENNReal.finset_sum_iSup_natₓ'. -/
theorem finset_sum_iSup_nat {α} {ι} [SemilatticeSup ι] {s : Finset α} {f : α → ι → ℝ≥0∞}
    (hf : ∀ a, Monotone (f a)) : (∑ a in s, iSup (f a)) = ⨆ n, ∑ a in s, f a n :=
  by
  refine' Finset.induction_on s _ _
  · simp
  · intro a s has ih
    simp only [Finset.sum_insert has]
    rw [ih, supr_add_supr_of_monotone (hf a)]
    intro i j h
    exact Finset.sum_le_sum fun a ha => hf a h
#align ennreal.finset_sum_supr_nat ENNReal.finset_sum_iSup_nat

/- warning: ennreal.mul_supr -> ENNReal.mul_iSup is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {a : ENNReal}, Eq.{1} ENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι f)) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (f i)))
but is expected to have type
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {a : ENNReal}, Eq.{1} ENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι f)) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (f i)))
Case conversion may be inaccurate. Consider using '#align ennreal.mul_supr ENNReal.mul_iSupₓ'. -/
theorem mul_iSup {ι : Sort _} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : a * iSup f = ⨆ i, a * f i :=
  by
  by_cases hf : ∀ i, f i = 0
  · obtain rfl : f = fun _ => 0
    exact funext hf
    simp only [supr_zero_eq_zero, MulZeroClass.mul_zero]
  · refine' (monotone_id.const_mul' _).map_iSup_of_continuousAt _ (MulZeroClass.mul_zero a)
    refine' ENNReal.Tendsto.const_mul tendsto_id (Or.inl _)
    exact mt supr_eq_zero.1 hf
#align ennreal.mul_supr ENNReal.mul_iSup

/- warning: ennreal.mul_Sup -> ENNReal.mul_sSup is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} ENNReal} {a : ENNReal}, Eq.{1} ENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (SupSet.sSup.{0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) s)) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ENNReal (fun (i : ENNReal) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) i s) (fun (H : Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) i s) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a i)))
but is expected to have type
  forall {s : Set.{0} ENNReal} {a : ENNReal}, Eq.{1} ENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (SupSet.sSup.{0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) s)) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ENNReal (fun (i : ENNReal) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) i s) (fun (H : Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) i s) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a i)))
Case conversion may be inaccurate. Consider using '#align ennreal.mul_Sup ENNReal.mul_sSupₓ'. -/
theorem mul_sSup {s : Set ℝ≥0∞} {a : ℝ≥0∞} : a * sSup s = ⨆ i ∈ s, a * i := by
  simp only [sSup_eq_iSup, mul_supr]
#align ennreal.mul_Sup ENNReal.mul_sSup

/- warning: ennreal.supr_mul -> ENNReal.iSup_mul is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {a : ENNReal}, Eq.{1} ENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι f) a) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f i) a))
but is expected to have type
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {a : ENNReal}, Eq.{1} ENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι f) a) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f i) a))
Case conversion may be inaccurate. Consider using '#align ennreal.supr_mul ENNReal.iSup_mulₓ'. -/
theorem iSup_mul {ι : Sort _} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : iSup f * a = ⨆ i, f i * a := by
  rw [mul_comm, mul_supr] <;> congr <;> funext <;> rw [mul_comm]
#align ennreal.supr_mul ENNReal.iSup_mul

theorem smul_iSup {ι : Sort _} {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (f : ι → ℝ≥0∞)
    (c : R) : (c • ⨆ i, f i) = ⨆ i, c • f i := by
  simp only [← smul_one_mul c (f _), ← smul_one_mul c (iSup _), ENNReal.mul_iSup]
#align ennreal.smul_supr ENNReal.smul_iSup

theorem smul_sSup {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (s : Set ℝ≥0∞) (c : R) :
    c • sSup s = ⨆ i ∈ s, c • i := by
  simp_rw [← smul_one_mul c (Sup _), ENNReal.mul_sSup, smul_one_mul]
#align ennreal.smul_Sup ENNReal.smul_sSup

/- warning: ennreal.supr_div -> ENNReal.iSup_div is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {a : ENNReal}, Eq.{1} ENNReal (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι f) a) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) (f i) a))
but is expected to have type
  forall {ι : Sort.{u1}} {f : ι -> ENNReal} {a : ENNReal}, Eq.{1} ENNReal (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι f) a) (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) (f i) a))
Case conversion may be inaccurate. Consider using '#align ennreal.supr_div ENNReal.iSup_divₓ'. -/
theorem iSup_div {ι : Sort _} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : iSup f / a = ⨆ i, f i / a :=
  iSup_mul
#align ennreal.supr_div ENNReal.iSup_div

/- warning: ennreal.tendsto_coe_sub -> ENNReal.tendsto_coe_sub is a dubious translation:
lean 3 declaration is
  forall {r : NNReal} {b : ENNReal}, Filter.Tendsto.{0, 0} ENNReal ENNReal (fun (b : ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) r) b) (nhds.{0} ENNReal ENNReal.topologicalSpace b) (nhds.{0} ENNReal ENNReal.topologicalSpace (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) r) b))
but is expected to have type
  forall {r : NNReal} {b : ENNReal}, Filter.Tendsto.{0, 0} ENNReal ENNReal (fun (b : ENNReal) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (ENNReal.some r) b) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal b) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (ENNReal.some r) b))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_coe_sub ENNReal.tendsto_coe_subₓ'. -/
protected theorem tendsto_coe_sub :
    ∀ {b : ℝ≥0∞}, Tendsto (fun b : ℝ≥0∞ => ↑r - b) (𝓝 b) (𝓝 (↑r - b)) :=
  by
  refine' forall_ennreal.2 ⟨fun a => _, _⟩
  · simp [@nhds_coe a, tendsto_map'_iff, (· ∘ ·), tendsto_coe, ← WithTop.coe_sub]
    exact tendsto_const_nhds.sub tendsto_id
  simp
  exact
    (tendsto.congr'
        (mem_of_superset (lt_mem_nhds <| @coe_lt_top r) <| by
          simp (config := { contextual := true }) [le_of_lt]))
      tendsto_const_nhds
#align ennreal.tendsto_coe_sub ENNReal.tendsto_coe_sub

/- warning: ennreal.sub_supr -> ENNReal.sub_iSup is a dubious translation:
lean 3 declaration is
  forall {a : ENNReal} {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {b : ι -> ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) a (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) a (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => b i))) (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) a (b i))))
but is expected to have type
  forall {a : ENNReal} {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {b : ι -> ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) a (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) a (iSup.{0, u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => b i))) (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) a (b i))))
Case conversion may be inaccurate. Consider using '#align ennreal.sub_supr ENNReal.sub_iSupₓ'. -/
theorem sub_iSup {ι : Sort _} [Nonempty ι] {b : ι → ℝ≥0∞} (hr : a < ⊤) :
    (a - ⨆ i, b i) = ⨅ i, a - b i :=
  by
  let ⟨r, Eq, _⟩ := lt_iff_exists_coe.mp hr
  have : sInf ((fun b => ↑r - b) '' range b) = ↑r - ⨆ i, b i :=
    IsGLB.sInf_eq <|
      isLUB_iSup.isGLB_of_tendsto (fun x _ y _ => tsub_le_tsub (le_refl (r : ℝ≥0∞)))
        (range_nonempty _) (ENNReal.tendsto_coe_sub.comp (tendsto_id'.2 inf_le_left))
  rw [Eq, ← this] <;> simp [sInf_image, iInf_range, -mem_range] <;> exact le_rfl
#align ennreal.sub_supr ENNReal.sub_iSup

/- warning: ennreal.exists_countable_dense_no_zero_top -> ENNReal.exists_countable_dense_no_zero_top is a dubious translation:
lean 3 declaration is
  Exists.{1} (Set.{0} ENNReal) (fun (s : Set.{0} ENNReal) => And (Set.Countable.{0} ENNReal s) (And (Dense.{0} ENNReal ENNReal.topologicalSpace s) (And (Not (Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) s)) (Not (Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) s)))))
but is expected to have type
  Exists.{1} (Set.{0} ENNReal) (fun (s : Set.{0} ENNReal) => And (Set.Countable.{0} ENNReal s) (And (Dense.{0} ENNReal ENNReal.instTopologicalSpaceENNReal s) (And (Not (Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) s)) (Not (Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) s)))))
Case conversion may be inaccurate. Consider using '#align ennreal.exists_countable_dense_no_zero_top ENNReal.exists_countable_dense_no_zero_topₓ'. -/
theorem exists_countable_dense_no_zero_top :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s :=
  by
  obtain ⟨s, s_count, s_dense, hs⟩ :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ (∀ x, IsBot x → x ∉ s) ∧ ∀ x, IsTop x → x ∉ s :=
    exists_countable_dense_no_bot_top ℝ≥0∞
  exact ⟨s, s_count, s_dense, fun h => hs.1 0 (by simp) h, fun h => hs.2 ∞ (by simp) h⟩
#align ennreal.exists_countable_dense_no_zero_top ENNReal.exists_countable_dense_no_zero_top

/- warning: ennreal.exists_lt_add_of_lt_add -> ENNReal.exists_lt_add_of_lt_add is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal} {z : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) y z)) -> (Ne.{1} ENNReal y (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Ne.{1} ENNReal z (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (y' : ENNReal) => Exists.{1} ENNReal (fun (z' : ENNReal) => And (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) y' y) (And (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) z' z) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) y' z'))))))
but is expected to have type
  forall {x : ENNReal} {y : ENNReal} {z : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) y z)) -> (Ne.{1} ENNReal y (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Ne.{1} ENNReal z (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (y' : ENNReal) => Exists.{1} ENNReal (fun (z' : ENNReal) => And (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) y' y) (And (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) z' z) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) y' z'))))))
Case conversion may be inaccurate. Consider using '#align ennreal.exists_lt_add_of_lt_add ENNReal.exists_lt_add_of_lt_addₓ'. -/
theorem exists_lt_add_of_lt_add {x y z : ℝ≥0∞} (h : x < y + z) (hy : y ≠ 0) (hz : z ≠ 0) :
    ∃ y' z', y' < y ∧ z' < z ∧ x < y' + z' :=
  by
  haveI : ne_bot (𝓝[<] y) := nhdsWithin_Iio_self_neBot' ⟨0, pos_iff_ne_zero.2 hy⟩
  haveI : ne_bot (𝓝[<] z) := nhdsWithin_Iio_self_neBot' ⟨0, pos_iff_ne_zero.2 hz⟩
  have A : tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 + p.2) ((𝓝[<] y).Prod (𝓝[<] z)) (𝓝 (y + z)) :=
    by
    apply tendsto.mono_left _ (Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds)
    rw [← nhds_prod_eq]
    exact tendsto_add
  rcases(((tendsto_order.1 A).1 x h).And
        (Filter.prod_mem_prod self_mem_nhdsWithin self_mem_nhdsWithin)).exists with
    ⟨⟨y', z'⟩, hx, hy', hz'⟩
  exact ⟨y', z', hy', hz', hx⟩
#align ennreal.exists_lt_add_of_lt_add ENNReal.exists_lt_add_of_lt_add

end TopologicalSpace

section Liminf

/- warning: ennreal.exists_frequently_lt_of_liminf_ne_top -> ENNReal.exists_frequently_lt_of_liminf_ne_top is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {l : Filter.{u1} ι} {x : ι -> Real}, (Ne.{1} ENNReal (Filter.liminf.{0, u1} ENNReal ι (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (n : ι) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) (fun (_x : MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) => Real -> NNReal) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) Real.nnabs (x n))) l) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Exists.{1} Real (fun (R : Real) => Filter.Frequently.{u1} ι (fun (n : ι) => LT.lt.{0} Real Real.hasLt (x n) R) l))
but is expected to have type
  forall {ι : Type.{u1}} {l : Filter.{u1} ι} {x : ι -> Real}, (Ne.{1} ENNReal (Filter.liminf.{0, u1} ENNReal ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (n : ι) => ENNReal.some (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real (fun (_x : Real) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Real) => NNReal) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulOneClass.toMul.{0} Real (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))) (MulOneClass.toMul.{0} NNReal (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))))) Real.nnabs (x n))) l) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Exists.{1} Real (fun (R : Real) => Filter.Frequently.{u1} ι (fun (n : ι) => LT.lt.{0} Real Real.instLTReal (x n) R) l))
Case conversion may be inaccurate. Consider using '#align ennreal.exists_frequently_lt_of_liminf_ne_top ENNReal.exists_frequently_lt_of_liminf_ne_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem exists_frequently_lt_of_liminf_ne_top {ι : Type _} {l : Filter ι} {x : ι → ℝ}
    (hx : liminf (fun n => ((x n).nnabs : ℝ≥0∞)) l ≠ ∞) : ∃ R, ∃ᶠ n in l, x n < R :=
  by
  by_contra h
  simp_rw [not_exists, not_frequently, not_lt] at h
  refine'
    hx
      (ENNReal.eq_top_of_forall_nnreal_le fun r =>
        le_Liminf_of_le
          (by
            run_tac
              is_bounded_default)
          _)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h r]with i hi using hi.trans (le_abs_self (x i))
#align ennreal.exists_frequently_lt_of_liminf_ne_top ENNReal.exists_frequently_lt_of_liminf_ne_top

/- warning: ennreal.exists_frequently_lt_of_liminf_ne_top' -> ENNReal.exists_frequently_lt_of_liminf_ne_top' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {l : Filter.{u1} ι} {x : ι -> Real}, (Ne.{1} ENNReal (Filter.liminf.{0, u1} ENNReal ι (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (n : ι) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) (fun (_x : MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) => Real -> NNReal) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) Real.nnabs (x n))) l) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Exists.{1} Real (fun (R : Real) => Filter.Frequently.{u1} ι (fun (n : ι) => LT.lt.{0} Real Real.hasLt R (x n)) l))
but is expected to have type
  forall {ι : Type.{u1}} {l : Filter.{u1} ι} {x : ι -> Real}, (Ne.{1} ENNReal (Filter.liminf.{0, u1} ENNReal ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (n : ι) => ENNReal.some (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real (fun (_x : Real) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Real) => NNReal) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulOneClass.toMul.{0} Real (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))) (MulOneClass.toMul.{0} NNReal (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))))) Real.nnabs (x n))) l) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Exists.{1} Real (fun (R : Real) => Filter.Frequently.{u1} ι (fun (n : ι) => LT.lt.{0} Real Real.instLTReal R (x n)) l))
Case conversion may be inaccurate. Consider using '#align ennreal.exists_frequently_lt_of_liminf_ne_top' ENNReal.exists_frequently_lt_of_liminf_ne_top'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem exists_frequently_lt_of_liminf_ne_top' {ι : Type _} {l : Filter ι} {x : ι → ℝ}
    (hx : liminf (fun n => ((x n).nnabs : ℝ≥0∞)) l ≠ ∞) : ∃ R, ∃ᶠ n in l, R < x n :=
  by
  by_contra h
  simp_rw [not_exists, not_frequently, not_lt] at h
  refine'
    hx
      (ENNReal.eq_top_of_forall_nnreal_le fun r =>
        le_Liminf_of_le
          (by
            run_tac
              is_bounded_default)
          _)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h (-r)]with i hi using(le_neg.1 hi).trans (neg_le_abs_self _)
#align ennreal.exists_frequently_lt_of_liminf_ne_top' ENNReal.exists_frequently_lt_of_liminf_ne_top'

/- warning: ennreal.exists_upcrossings_of_not_bounded_under -> ENNReal.exists_upcrossings_of_not_bounded_under is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {l : Filter.{u1} ι} {x : ι -> Real}, (Ne.{1} ENNReal (Filter.liminf.{0, u1} ENNReal ι (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (i : ι) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) (fun (_x : MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) => Real -> NNReal) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) Real.nnabs (x i))) l) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Not (Filter.IsBoundedUnder.{0, u1} Real ι (LE.le.{0} Real Real.hasLe) l (fun (i : ι) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (x i)))) -> (Exists.{1} Rat (fun (a : Rat) => Exists.{1} Rat (fun (b : Rat) => And (LT.lt.{0} Rat Rat.hasLt a b) (And (Filter.Frequently.{u1} ι (fun (i : ι) => LT.lt.{0} Real Real.hasLt (x i) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) a)) l) (Filter.Frequently.{u1} ι (fun (i : ι) => LT.lt.{0} Real Real.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) b) (x i)) l)))))
but is expected to have type
  forall {ι : Type.{u1}} {l : Filter.{u1} ι} {x : ι -> Real}, (Ne.{1} ENNReal (Filter.liminf.{0, u1} ENNReal ι (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (i : ι) => ENNReal.some (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real (fun (_x : Real) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Real) => NNReal) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulOneClass.toMul.{0} Real (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))) (MulOneClass.toMul.{0} NNReal (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))))) Real.nnabs (x i))) l) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Not (Filter.IsBoundedUnder.{0, u1} Real ι (fun (x._@.Mathlib.Topology.Instances.ENNReal._hyg.14713 : Real) (x._@.Mathlib.Topology.Instances.ENNReal._hyg.14715 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Topology.Instances.ENNReal._hyg.14713 x._@.Mathlib.Topology.Instances.ENNReal._hyg.14715) l (fun (i : ι) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (x i)))) -> (Exists.{1} Rat (fun (a : Rat) => Exists.{1} Rat (fun (b : Rat) => And (LT.lt.{0} Rat Rat.instLTRat_1 a b) (And (Filter.Frequently.{u1} ι (fun (i : ι) => LT.lt.{0} Real Real.instLTReal (x i) (Rat.cast.{0} Real Real.ratCast a)) l) (Filter.Frequently.{u1} ι (fun (i : ι) => LT.lt.{0} Real Real.instLTReal (Rat.cast.{0} Real Real.ratCast b) (x i)) l)))))
Case conversion may be inaccurate. Consider using '#align ennreal.exists_upcrossings_of_not_bounded_under ENNReal.exists_upcrossings_of_not_bounded_underₓ'. -/
theorem exists_upcrossings_of_not_bounded_under {ι : Type _} {l : Filter ι} {x : ι → ℝ}
    (hf : liminf (fun i => ((x i).nnabs : ℝ≥0∞)) l ≠ ∞)
    (hbdd : ¬IsBoundedUnder (· ≤ ·) l fun i => |x i|) :
    ∃ a b : ℚ, a < b ∧ (∃ᶠ i in l, x i < a) ∧ ∃ᶠ i in l, ↑b < x i :=
  by
  rw [is_bounded_under_le_abs, not_and_or] at hbdd
  obtain hbdd | hbdd := hbdd
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top hf
    obtain ⟨q, hq⟩ := exists_rat_gt R
    refine' ⟨q, q + 1, (lt_add_iff_pos_right _).2 zero_lt_one, _, _⟩
    · refine' fun hcon => hR _
      filter_upwards [hcon]with x hx using not_lt.2 (lt_of_lt_of_le hq (not_lt.1 hx)).le
    · simp only [is_bounded_under, is_bounded, eventually_map, eventually_at_top, ge_iff_le,
        not_exists, not_forall, not_le, exists_prop] at hbdd
      refine' fun hcon => hbdd ↑(q + 1) _
      filter_upwards [hcon]with x hx using not_lt.1 hx
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top' hf
    obtain ⟨q, hq⟩ := exists_rat_lt R
    refine' ⟨q - 1, q, (sub_lt_self_iff _).2 zero_lt_one, _, _⟩
    · simp only [is_bounded_under, is_bounded, eventually_map, eventually_at_top, ge_iff_le,
        not_exists, not_forall, not_le, exists_prop] at hbdd
      refine' fun hcon => hbdd ↑(q - 1) _
      filter_upwards [hcon]with x hx using not_lt.1 hx
    · refine' fun hcon => hR _
      filter_upwards [hcon]with x hx using not_lt.2 ((not_lt.1 hx).trans hq.le)
#align ennreal.exists_upcrossings_of_not_bounded_under ENNReal.exists_upcrossings_of_not_bounded_under

end Liminf

section tsum

variable {f g : α → ℝ≥0∞}

/- warning: ennreal.has_sum_coe -> ENNReal.hasSum_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal} {r : NNReal}, Iff (HasSum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f a)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) r)) (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f r)
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal} {r : NNReal}, Iff (HasSum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (fun (a : α) => ENNReal.some (f a)) (ENNReal.some r)) (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f r)
Case conversion may be inaccurate. Consider using '#align ennreal.has_sum_coe ENNReal.hasSum_coeₓ'. -/
@[norm_cast]
protected theorem hasSum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
    HasSum (fun a => (f a : ℝ≥0∞)) ↑r ↔ HasSum f r :=
  by
  have :
    (fun s : Finset α => ∑ a in s, ↑(f a)) =
      (coe : ℝ≥0 → ℝ≥0∞) ∘ fun s : Finset α => ∑ a in s, f a :=
    funext fun s => ENNReal.coe_finset_sum.symm
  unfold HasSum <;> rw [this, tendsto_coe]
#align ennreal.has_sum_coe ENNReal.hasSum_coe

/- warning: ennreal.tsum_coe_eq -> ENNReal.tsum_coe_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : NNReal} {f : α -> NNReal}, (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f r) -> (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f a))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) r))
but is expected to have type
  forall {α : Type.{u1}} {r : NNReal} {f : α -> NNReal}, (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f r) -> (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => ENNReal.some (f a))) (ENNReal.some r))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_coe_eq ENNReal.tsum_coe_eqₓ'. -/
protected theorem tsum_coe_eq {f : α → ℝ≥0} (h : HasSum f r) : (∑' a, (f a : ℝ≥0∞)) = r :=
  (ENNReal.hasSum_coe.2 h).tsum_eq
#align ennreal.tsum_coe_eq ENNReal.tsum_coe_eq

/- warning: ennreal.coe_tsum -> ENNReal.coe_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) -> (Eq.{1} ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α f)) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f a))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) -> (Eq.{1} ENNReal (ENNReal.some (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α f)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => ENNReal.some (f a))))
Case conversion may be inaccurate. Consider using '#align ennreal.coe_tsum ENNReal.coe_tsumₓ'. -/
protected theorem coe_tsum {f : α → ℝ≥0} : Summable f → ↑(tsum f) = ∑' a, (f a : ℝ≥0∞)
  | ⟨r, hr⟩ => by rw [hr.tsum_eq, ENNReal.tsum_coe_eq hr]
#align ennreal.coe_tsum ENNReal.coe_tsum

/- warning: ennreal.has_sum -> ENNReal.hasSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, HasSum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace f (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Finset.{u1} α) (fun (s : Finset.{u1} α) => Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, HasSum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal f (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Finset.{u1} α) (fun (s : Finset.{u1} α) => Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align ennreal.has_sum ENNReal.hasSumₓ'. -/
protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a in s, f a) :=
  tendsto_atTop_iSup fun s t => Finset.sum_le_sum_of_subset
#align ennreal.has_sum ENNReal.hasSum

/- warning: ennreal.summable -> ENNReal.summable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, Summable.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace f
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, Summable.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal f
Case conversion may be inaccurate. Consider using '#align ennreal.summable ENNReal.summableₓ'. -/
@[simp]
protected theorem summable : Summable f :=
  ⟨_, ENNReal.hasSum⟩
#align ennreal.summable ENNReal.summable

/- warning: ennreal.tsum_coe_ne_top_iff_summable -> ENNReal.tsum_coe_ne_top_iff_summable is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {f : β -> NNReal}, Iff (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (b : β) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f b))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Summable.{0, u1} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f)
but is expected to have type
  forall {β : Type.{u1}} {f : β -> NNReal}, Iff (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (b : β) => ENNReal.some (f b))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Summable.{0, u1} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f)
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_coe_ne_top_iff_summable ENNReal.tsum_coe_ne_top_iff_summableₓ'. -/
theorem tsum_coe_ne_top_iff_summable {f : β → ℝ≥0} : (∑' b, (f b : ℝ≥0∞)) ≠ ∞ ↔ Summable f :=
  by
  refine' ⟨fun h => _, fun h => ENNReal.coe_tsum h ▸ ENNReal.coe_ne_top⟩
  lift ∑' b, (f b : ℝ≥0∞) to ℝ≥0 using h with a ha
  refine' ⟨a, ENNReal.hasSum_coe.1 _⟩
  rw [ha]
  exact ennreal.summable.has_sum
#align ennreal.tsum_coe_ne_top_iff_summable ENNReal.tsum_coe_ne_top_iff_summable

/- warning: ennreal.tsum_eq_supr_sum -> ENNReal.tsum_eq_iSup_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a)) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Finset.{u1} α) (fun (s : Finset.{u1} α) => Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a)) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Finset.{u1} α) (fun (s : Finset.{u1} α) => Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_eq_supr_sum ENNReal.tsum_eq_iSup_sumₓ'. -/
protected theorem tsum_eq_iSup_sum : (∑' a, f a) = ⨆ s : Finset α, ∑ a in s, f a :=
  ENNReal.hasSum.tsum_eq
#align ennreal.tsum_eq_supr_sum ENNReal.tsum_eq_iSup_sum

/- warning: ennreal.tsum_eq_supr_sum' -> ENNReal.tsum_eq_iSup_sum' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} {ι : Type.{u2}} (s : ι -> (Finset.{u1} α)), (forall (t : Finset.{u1} α), Exists.{succ u2} ι (fun (i : ι) => HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) t (s i))) -> (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a)) (iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (s i) (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} {ι : Type.{u2}} (s : ι -> (Finset.{u1} α)), (forall (t : Finset.{u1} α), Exists.{succ u2} ι (fun (i : ι) => HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) t (s i))) -> (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a)) (iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (s i) (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_eq_supr_sum' ENNReal.tsum_eq_iSup_sum'ₓ'. -/
protected theorem tsum_eq_iSup_sum' {ι : Type _} (s : ι → Finset α) (hs : ∀ t, ∃ i, t ⊆ s i) :
    (∑' a, f a) = ⨆ i, ∑ a in s i, f a :=
  by
  rw [ENNReal.tsum_eq_iSup_sum]
  symm
  change (⨆ i : ι, (fun t : Finset α => ∑ a in t, f a) (s i)) = ⨆ s : Finset α, ∑ a in s, f a
  exact (Finset.sum_mono_set f).iSup_comp_eq hs
#align ennreal.tsum_eq_supr_sum' ENNReal.tsum_eq_iSup_sum'

/- warning: ennreal.tsum_sigma -> ENNReal.tsum_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} (f : forall (a : α), (β a) -> ENNReal), Eq.{1} ENNReal (tsum.{0, max u1 u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (Sigma.{u1, u2} α (fun (a : α) => β a)) (fun (p : Sigma.{u1, u2} α (fun (a : α) => β a)) => f (Sigma.fst.{u1, u2} α (fun (a : α) => β a) p) (Sigma.snd.{u1, u2} α (fun (a : α) => β a) p))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (β a) (fun (b : β a) => f a b)))
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} (f : forall (a : α), (β a) -> ENNReal), Eq.{1} ENNReal (tsum.{0, max u1 u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Sigma.{u1, u2} α (fun (a : α) => β a)) (fun (p : Sigma.{u1, u2} α (fun (a : α) => β a)) => f (Sigma.fst.{u1, u2} α (fun (a : α) => β a) p) (Sigma.snd.{u1, u2} α (fun (a : α) => β a) p))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (β a) (fun (b : β a) => f a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_sigma ENNReal.tsum_sigmaₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
protected theorem tsum_sigma {β : α → Type _} (f : ∀ a, β a → ℝ≥0∞) :
    (∑' p : Σa, β a, f p.1 p.2) = ∑' (a) (b), f a b :=
  tsum_sigma' (fun b => ENNReal.summable) ENNReal.summable
#align ennreal.tsum_sigma ENNReal.tsum_sigma

/- warning: ennreal.tsum_sigma' -> ENNReal.tsum_sigma' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} (f : (Sigma.{u1, u2} α (fun (a : α) => β a)) -> ENNReal), Eq.{1} ENNReal (tsum.{0, max u1 u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (Sigma.{u1, u2} α (fun (a : α) => β a)) (fun (p : Sigma.{u1, u2} α (fun (a : α) => β a)) => f p)) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (β a) (fun (b : β a) => f (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a b))))
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} (f : (Sigma.{u1, u2} α (fun (a : α) => β a)) -> ENNReal), Eq.{1} ENNReal (tsum.{0, max u1 u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Sigma.{u1, u2} α (fun (a : α) => β a)) (fun (p : Sigma.{u1, u2} α (fun (a : α) => β a)) => f p)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (β a) (fun (b : β a) => f (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a b))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_sigma' ENNReal.tsum_sigma'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
protected theorem tsum_sigma' {β : α → Type _} (f : (Σa, β a) → ℝ≥0∞) :
    (∑' p : Σa, β a, f p) = ∑' (a) (b), f ⟨a, b⟩ :=
  tsum_sigma' (fun b => ENNReal.summable) ENNReal.summable
#align ennreal.tsum_sigma' ENNReal.tsum_sigma'

/- warning: ennreal.tsum_prod -> ENNReal.tsum_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β -> ENNReal}, Eq.{1} ENNReal (tsum.{0, max u1 u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (Prod.{u1, u2} α β) (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (b : β) => f a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β -> ENNReal}, Eq.{1} ENNReal (tsum.{0, max u2 u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Prod.{u2, u1} α β) (fun (p : Prod.{u2, u1} α β) => f (Prod.fst.{u2, u1} α β p) (Prod.snd.{u2, u1} α β p))) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (b : β) => f a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_prod ENNReal.tsum_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
protected theorem tsum_prod {f : α → β → ℝ≥0∞} : (∑' p : α × β, f p.1 p.2) = ∑' (a) (b), f a b :=
  tsum_prod' ENNReal.summable fun _ => ENNReal.summable
#align ennreal.tsum_prod ENNReal.tsum_prod

/- warning: ennreal.tsum_prod' -> ENNReal.tsum_prod' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : (Prod.{u1, u2} α β) -> ENNReal}, Eq.{1} ENNReal (tsum.{0, max u1 u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (Prod.{u1, u2} α β) (fun (p : Prod.{u1, u2} α β) => f p)) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (b : β) => f (Prod.mk.{u1, u2} α β a b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : (Prod.{u2, u1} α β) -> ENNReal}, Eq.{1} ENNReal (tsum.{0, max u2 u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Prod.{u2, u1} α β) (fun (p : Prod.{u2, u1} α β) => f p)) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (b : β) => f (Prod.mk.{u2, u1} α β a b))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_prod' ENNReal.tsum_prod'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
protected theorem tsum_prod' {f : α × β → ℝ≥0∞} : (∑' p : α × β, f p) = ∑' (a) (b), f (a, b) :=
  tsum_prod' ENNReal.summable fun _ => ENNReal.summable
#align ennreal.tsum_prod' ENNReal.tsum_prod'

/- warning: ennreal.tsum_comm -> ENNReal.tsum_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (b : β) => f a b))) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (b : β) => tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (b : β) => f a b))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (b : β) => tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a b)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_comm ENNReal.tsum_commₓ'. -/
protected theorem tsum_comm {f : α → β → ℝ≥0∞} : (∑' a, ∑' b, f a b) = ∑' b, ∑' a, f a b :=
  tsum_comm' ENNReal.summable (fun _ => ENNReal.summable) fun _ => ENNReal.summable
#align ennreal.tsum_comm ENNReal.tsum_comm

/- warning: ennreal.tsum_add -> ENNReal.tsum_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} {g : α -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => g a)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} {g : α -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => g a)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_add ENNReal.tsum_addₓ'. -/
protected theorem tsum_add : (∑' a, f a + g a) = (∑' a, f a) + ∑' a, g a :=
  tsum_add ENNReal.summable ENNReal.summable
#align ennreal.tsum_add ENNReal.tsum_add

/- warning: ennreal.tsum_le_tsum -> ENNReal.tsum_le_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} {g : α -> ENNReal}, (forall (a : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f a) (g a)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => g a)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} {g : α -> ENNReal}, (forall (a : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f a) (g a)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => g a)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_le_tsum ENNReal.tsum_le_tsumₓ'. -/
protected theorem tsum_le_tsum (h : ∀ a, f a ≤ g a) : (∑' a, f a) ≤ ∑' a, g a :=
  tsum_le_tsum h ENNReal.summable ENNReal.summable
#align ennreal.tsum_le_tsum ENNReal.tsum_le_tsum

/- warning: ennreal.sum_le_tsum -> ENNReal.sum_le_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} (s : Finset.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (x : α) => f x)) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => f x))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} (s : Finset.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (x : α) => f x)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => f x))
Case conversion may be inaccurate. Consider using '#align ennreal.sum_le_tsum ENNReal.sum_le_tsumₓ'. -/
protected theorem sum_le_tsum {f : α → ℝ≥0∞} (s : Finset α) : (∑ x in s, f x) ≤ ∑' x, f x :=
  sum_le_tsum s (fun x hx => zero_le _) ENNReal.summable
#align ennreal.sum_le_tsum ENNReal.sum_le_tsum

/- warning: ennreal.tsum_eq_supr_nat' -> ENNReal.tsum_eq_iSup_nat' is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> ENNReal} {N : Nat -> Nat}, (Filter.Tendsto.{0, 0} Nat Nat N (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) -> (Eq.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => f i)) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (i : Nat) => Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.range (N i)) (fun (a : Nat) => f a))))
but is expected to have type
  forall {f : Nat -> ENNReal} {N : Nat -> Nat}, (Filter.Tendsto.{0, 0} Nat Nat N (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) -> (Eq.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => f i)) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (i : Nat) => Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.range (N i)) (fun (a : Nat) => f a))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_eq_supr_nat' ENNReal.tsum_eq_iSup_nat'ₓ'. -/
protected theorem tsum_eq_iSup_nat' {f : ℕ → ℝ≥0∞} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    (∑' i : ℕ, f i) = ⨆ i : ℕ, ∑ a in Finset.range (N i), f a :=
  ENNReal.tsum_eq_iSup_sum' _ fun t =>
    let ⟨n, hn⟩ := t.exists_nat_subset_range
    let ⟨k, _, hk⟩ := exists_le_of_tendsto_atTop hN 0 n
    ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩
#align ennreal.tsum_eq_supr_nat' ENNReal.tsum_eq_iSup_nat'

/- warning: ennreal.tsum_eq_supr_nat -> ENNReal.tsum_eq_iSup_nat is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> ENNReal}, Eq.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => f i)) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (i : Nat) => Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.range i) (fun (a : Nat) => f a)))
but is expected to have type
  forall {f : Nat -> ENNReal}, Eq.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => f i)) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (i : Nat) => Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.range i) (fun (a : Nat) => f a)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_eq_supr_nat ENNReal.tsum_eq_iSup_natₓ'. -/
protected theorem tsum_eq_iSup_nat {f : ℕ → ℝ≥0∞} :
    (∑' i : ℕ, f i) = ⨆ i : ℕ, ∑ a in Finset.range i, f a :=
  ENNReal.tsum_eq_iSup_sum' _ Finset.exists_nat_subset_range
#align ennreal.tsum_eq_supr_nat ENNReal.tsum_eq_iSup_nat

/- warning: ennreal.tsum_eq_liminf_sum_nat -> ENNReal.tsum_eq_liminf_sum_nat is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> ENNReal}, Eq.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => f i)) (Filter.liminf.{0, 0} ENNReal Nat (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (n : Nat) => Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))))
but is expected to have type
  forall {f : Nat -> ENNReal}, Eq.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => f i)) (Filter.liminf.{0, 0} ENNReal Nat (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (n : Nat) => Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_eq_liminf_sum_nat ENNReal.tsum_eq_liminf_sum_natₓ'. -/
protected theorem tsum_eq_liminf_sum_nat {f : ℕ → ℝ≥0∞} :
    (∑' i, f i) = liminf (fun n => ∑ i in Finset.range n, f i) atTop :=
  by
  rw [ENNReal.tsum_eq_iSup_nat, Filter.liminf_eq_iSup_iInf_of_nat]
  congr
  refine' funext fun n => le_antisymm _ _
  · refine' le_iInf₂ fun i hi => Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => zero_le _
    simpa only [Finset.range_subset, add_le_add_iff_right] using hi
  · refine' le_trans (iInf_le _ n) _
    simp [le_refl n, le_refl ((Finset.range n).Sum f)]
#align ennreal.tsum_eq_liminf_sum_nat ENNReal.tsum_eq_liminf_sum_nat

/- warning: ennreal.le_tsum -> ENNReal.le_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} (a : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f a) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} (a : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f a) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a))
Case conversion may be inaccurate. Consider using '#align ennreal.le_tsum ENNReal.le_tsumₓ'. -/
protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
  le_tsum' ENNReal.summable a
#align ennreal.le_tsum ENNReal.le_tsum

/- warning: ennreal.tsum_eq_zero -> ENNReal.tsum_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, Iff (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (i : α) => f i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (forall (i : α), Eq.{1} ENNReal (f i) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, Iff (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (i : α) => f i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall (i : α), Eq.{1} ENNReal (f i) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_eq_zero ENNReal.tsum_eq_zeroₓ'. -/
@[simp]
protected theorem tsum_eq_zero : (∑' i, f i) = 0 ↔ ∀ i, f i = 0 :=
  ⟨fun h i => nonpos_iff_eq_zero.1 <| h ▸ ENNReal.le_tsum i, fun h => by simp [h]⟩
#align ennreal.tsum_eq_zero ENNReal.tsum_eq_zero

/- warning: ennreal.tsum_eq_top_of_eq_top -> ENNReal.tsum_eq_top_of_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Exists.{succ u1} α (fun (a : α) => Eq.{1} ENNReal (f a) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Exists.{succ u1} α (fun (a : α) => Eq.{1} ENNReal (f a) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_eq_top_of_eq_top ENNReal.tsum_eq_top_of_eq_topₓ'. -/
protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ∞) → (∑' a, f a) = ∞
  | ⟨a, ha⟩ => top_unique <| ha ▸ ENNReal.le_tsum a
#align ennreal.tsum_eq_top_of_eq_top ENNReal.tsum_eq_top_of_eq_top

/- warning: ennreal.lt_top_of_tsum_ne_top -> ENNReal.lt_top_of_tsum_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (i : α) => a i)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall (j : α), LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (a j) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} {a : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (i : α) => a i)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall (j : α), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (a j) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.lt_top_of_tsum_ne_top ENNReal.lt_top_of_tsum_ne_topₓ'. -/
protected theorem lt_top_of_tsum_ne_top {a : α → ℝ≥0∞} (tsum_ne_top : (∑' i, a i) ≠ ∞) (j : α) :
    a j < ∞ := by
  have key := not_imp_not.mpr ENNReal.tsum_eq_top_of_eq_top
  simp only [not_exists] at key
  exact lt_top_iff_ne_top.mpr (key tsum_ne_top j)
#align ennreal.lt_top_of_tsum_ne_top ENNReal.lt_top_of_tsum_ne_top

/- warning: ennreal.tsum_top -> ENNReal.tsum_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Nonempty.{succ u1} α], Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Nonempty.{succ u1} α], Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_top ENNReal.tsum_topₓ'. -/
@[simp]
protected theorem tsum_top [Nonempty α] : (∑' a : α, ∞) = ∞ :=
  let ⟨a⟩ := ‹Nonempty α›
  ENNReal.tsum_eq_top_of_eq_top ⟨a, rfl⟩
#align ennreal.tsum_top ENNReal.tsum_top

/- warning: ennreal.tsum_const_eq_top_of_ne_zero -> ENNReal.tsum_const_eq_top_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] {c : ENNReal}, (Ne.{1} ENNReal c (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => c)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] {c : ENNReal}, (Ne.{1} ENNReal c (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => c)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_const_eq_top_of_ne_zero ENNReal.tsum_const_eq_top_of_ne_zeroₓ'. -/
theorem tsum_const_eq_top_of_ne_zero {α : Type _} [Infinite α] {c : ℝ≥0∞} (hc : c ≠ 0) :
    (∑' a : α, c) = ∞ :=
  by
  have A : tendsto (fun n : ℕ => (n : ℝ≥0∞) * c) at_top (𝓝 (∞ * c)) :=
    by
    apply ENNReal.Tendsto.mul_const tendsto_nat_nhds_top
    simp only [true_or_iff, top_ne_zero, Ne.def, not_false_iff]
  have B : ∀ n : ℕ, (n : ℝ≥0∞) * c ≤ ∑' a : α, c :=
    by
    intro n
    rcases Infinite.exists_subset_card_eq α n with ⟨s, hs⟩
    simpa [hs] using @ENNReal.sum_le_tsum α (fun i => c) s
  simpa [hc] using le_of_tendsto' A B
#align ennreal.tsum_const_eq_top_of_ne_zero ENNReal.tsum_const_eq_top_of_ne_zero

/- warning: ennreal.ne_top_of_tsum_ne_top -> ENNReal.ne_top_of_tsum_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall (a : α), Ne.{1} ENNReal (f a) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall (a : α), Ne.{1} ENNReal (f a) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.ne_top_of_tsum_ne_top ENNReal.ne_top_of_tsum_ne_topₓ'. -/
protected theorem ne_top_of_tsum_ne_top (h : (∑' a, f a) ≠ ∞) (a : α) : f a ≠ ∞ := fun ha =>
  h <| ENNReal.tsum_eq_top_of_eq_top ⟨a, ha⟩
#align ennreal.ne_top_of_tsum_ne_top ENNReal.ne_top_of_tsum_ne_top

/- warning: ennreal.tsum_mul_left -> ENNReal.tsum_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : ENNReal} {f : α -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (i : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (f i))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (i : α) => f i)))
but is expected to have type
  forall {α : Type.{u1}} {a : ENNReal} {f : α -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (i : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (f i))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_mul_left ENNReal.tsum_mul_leftₓ'. -/
protected theorem tsum_mul_left : (∑' i, a * f i) = a * ∑' i, f i :=
  if h : ∀ i, f i = 0 then by simp [h]
  else
    let ⟨i, (hi : f i ≠ 0)⟩ := not_forall.mp h
    have sum_ne_0 : (∑' i, f i) ≠ 0 :=
      ne_of_gt <|
        calc
          0 < f i := lt_of_le_of_ne (zero_le _) hi.symm
          _ ≤ ∑' i, f i := ENNReal.le_tsum _
          
    have : Tendsto (fun s : Finset α => ∑ j in s, a * f j) atTop (𝓝 (a * ∑' i, f i)) := by
      rw [←
          show ((· * ·) a ∘ fun s : Finset α => ∑ j in s, f j) = fun s => ∑ j in s, a * f j from
            funext fun s => Finset.mul_sum] <;>
        exact ENNReal.Tendsto.const_mul ennreal.summable.has_sum (Or.inl sum_ne_0)
    HasSum.tsum_eq this
#align ennreal.tsum_mul_left ENNReal.tsum_mul_left

/- warning: ennreal.tsum_mul_right -> ENNReal.tsum_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : ENNReal} {f : α -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (i : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f i) a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (i : α) => f i)) a)
but is expected to have type
  forall {α : Type.{u1}} {a : ENNReal} {f : α -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (i : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f i) a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (i : α) => f i)) a)
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_mul_right ENNReal.tsum_mul_rightₓ'. -/
protected theorem tsum_mul_right : (∑' i, f i * a) = (∑' i, f i) * a := by
  simp [mul_comm, ENNReal.tsum_mul_left]
#align ennreal.tsum_mul_right ENNReal.tsum_mul_right

protected theorem tsum_const_smul {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (a : R) :
    (∑' i, a • f i) = a • ∑' i, f i := by
  simpa only [smul_one_mul] using @ENNReal.tsum_mul_left _ (a • 1) _
#align ennreal.tsum_const_smul ENNReal.tsum_const_smul

/- warning: ennreal.tsum_supr_eq -> ENNReal.tsum_iSup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) {f : α -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (b : α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Eq.{succ u1} α a b) (fun (h : Eq.{succ u1} α a b) => f b))) (f a)
but is expected to have type
  forall {α : Type.{u1}} (a : α) {f : α -> ENNReal}, Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (b : α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Eq.{succ u1} α a b) (fun (h : Eq.{succ u1} α a b) => f b))) (f a)
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_supr_eq ENNReal.tsum_iSup_eqₓ'. -/
@[simp]
theorem tsum_iSup_eq {α : Type _} (a : α) {f : α → ℝ≥0∞} : (∑' b : α, ⨆ h : a = b, f b) = f a :=
  le_antisymm
    (by
      rw [ENNReal.tsum_eq_iSup_sum] <;>
        exact
          iSup_le fun s =>
            calc
              (∑ b in s, ⨆ h : a = b, f b) ≤ ∑ b in {a}, ⨆ h : a = b, f b :=
                Finset.sum_le_sum_of_ne_zero fun b _ hb =>
                  suffices a = b by simpa using this.symm
                  by_contradiction fun h => by simpa [h] using hb
              _ = f a := by simp
              )
    (calc
      f a ≤ ⨆ h : a = a, f a := le_iSup (fun h : a = a => f a) rfl
      _ ≤ ∑' b : α, ⨆ h : a = b, f b := ENNReal.le_tsum _
      )
#align ennreal.tsum_supr_eq ENNReal.tsum_iSup_eq

/- warning: ennreal.has_sum_iff_tendsto_nat -> ENNReal.hasSum_iff_tendsto_nat is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> ENNReal} (r : ENNReal), Iff (HasSum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace f r) (Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace r))
but is expected to have type
  forall {f : Nat -> ENNReal} (r : ENNReal), Iff (HasSum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal f r) (Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal r))
Case conversion may be inaccurate. Consider using '#align ennreal.has_sum_iff_tendsto_nat ENNReal.hasSum_iff_tendsto_natₓ'. -/
theorem hasSum_iff_tendsto_nat {f : ℕ → ℝ≥0∞} (r : ℝ≥0∞) :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop (𝓝 r) :=
  by
  refine' ⟨HasSum.tendsto_sum_nat, fun h => _⟩
  rw [← iSup_eq_of_tendsto _ h, ← ENNReal.tsum_eq_iSup_nat]
  · exact ennreal.summable.has_sum
  · exact fun s t hst => Finset.sum_le_sum_of_subset (Finset.range_subset.2 hst)
#align ennreal.has_sum_iff_tendsto_nat ENNReal.hasSum_iff_tendsto_nat

/- warning: ennreal.tendsto_nat_tsum -> ENNReal.tendsto_nat_tsum is a dubious translation:
lean 3 declaration is
  forall (f : Nat -> ENNReal), Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => f n)))
but is expected to have type
  forall (f : Nat -> ENNReal), Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => f n)))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_nat_tsum ENNReal.tendsto_nat_tsumₓ'. -/
theorem tendsto_nat_tsum (f : ℕ → ℝ≥0∞) :
    Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop (𝓝 (∑' n, f n)) :=
  by
  rw [← has_sum_iff_tendsto_nat]
  exact ennreal.summable.has_sum
#align ennreal.tendsto_nat_tsum ENNReal.tendsto_nat_tsum

/- warning: ennreal.to_nnreal_apply_of_tsum_ne_top -> ENNReal.toNNReal_apply_of_tsum_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (i : α) => f i)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall (x : α), Eq.{1} ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (Function.comp.{succ u1, 1, 1} α ENNReal NNReal ENNReal.toNNReal f x)) (f x))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (i : α) => f i)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall (x : α), Eq.{1} ENNReal (ENNReal.some (Function.comp.{succ u1, 1, 1} α ENNReal NNReal ENNReal.toNNReal f x)) (f x))
Case conversion may be inaccurate. Consider using '#align ennreal.to_nnreal_apply_of_tsum_ne_top ENNReal.toNNReal_apply_of_tsum_ne_topₓ'. -/
theorem toNNReal_apply_of_tsum_ne_top {α : Type _} {f : α → ℝ≥0∞} (hf : (∑' i, f i) ≠ ∞) (x : α) :
    (((ENNReal.toNNReal ∘ f) x : ℝ≥0) : ℝ≥0∞) = f x :=
  coe_toNNReal <| ENNReal.ne_top_of_tsum_ne_top hf _
#align ennreal.to_nnreal_apply_of_tsum_ne_top ENNReal.toNNReal_apply_of_tsum_ne_top

/- warning: ennreal.summable_to_nnreal_of_tsum_ne_top -> ENNReal.summable_toNNReal_of_tsum_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (i : α) => f i)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (Function.comp.{succ u1, 1, 1} α ENNReal NNReal ENNReal.toNNReal f))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (i : α) => f i)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (Function.comp.{succ u1, 1, 1} α ENNReal NNReal ENNReal.toNNReal f))
Case conversion may be inaccurate. Consider using '#align ennreal.summable_to_nnreal_of_tsum_ne_top ENNReal.summable_toNNReal_of_tsum_ne_topₓ'. -/
theorem summable_toNNReal_of_tsum_ne_top {α : Type _} {f : α → ℝ≥0∞} (hf : (∑' i, f i) ≠ ∞) :
    Summable (ENNReal.toNNReal ∘ f) := by
  simpa only [← tsum_coe_ne_top_iff_summable, to_nnreal_apply_of_tsum_ne_top hf] using hf
#align ennreal.summable_to_nnreal_of_tsum_ne_top ENNReal.summable_toNNReal_of_tsum_ne_top

/- warning: ennreal.tendsto_cofinite_zero_of_tsum_ne_top -> ENNReal.tendsto_cofinite_zero_of_tsum_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Tendsto.{u1, 0} α ENNReal f (Filter.cofinite.{u1} α) (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Tendsto.{u1, 0} α ENNReal f (Filter.cofinite.{u1} α) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_cofinite_zero_of_tsum_ne_top ENNReal.tendsto_cofinite_zero_of_tsum_ne_topₓ'. -/
theorem tendsto_cofinite_zero_of_tsum_ne_top {α} {f : α → ℝ≥0∞} (hf : (∑' x, f x) ≠ ∞) :
    Tendsto f cofinite (𝓝 0) :=
  by
  have f_ne_top : ∀ n, f n ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hf
  have h_f_coe : f = fun n => ((f n).toNNReal : ENNReal) :=
    funext fun n => (coe_to_nnreal (f_ne_top n)).symm
  rw [h_f_coe, ← @coe_zero, tendsto_coe]
  exact NNReal.tendsto_cofinite_zero_of_summable (summable_to_nnreal_of_tsum_ne_top hf)
#align ennreal.tendsto_cofinite_zero_of_tsum_ne_top ENNReal.tendsto_cofinite_zero_of_tsum_ne_top

/- warning: ennreal.tendsto_at_top_zero_of_tsum_ne_top -> ENNReal.tendsto_atTop_zero_of_tsum_ne_top is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (x : Nat) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Tendsto.{0, 0} Nat ENNReal f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {f : Nat -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (x : Nat) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Tendsto.{0, 0} Nat ENNReal f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_at_top_zero_of_tsum_ne_top ENNReal.tendsto_atTop_zero_of_tsum_ne_topₓ'. -/
theorem tendsto_atTop_zero_of_tsum_ne_top {f : ℕ → ℝ≥0∞} (hf : (∑' x, f x) ≠ ∞) :
    Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_tsum_ne_top hf
#align ennreal.tendsto_at_top_zero_of_tsum_ne_top ENNReal.tendsto_atTop_zero_of_tsum_ne_top

/- warning: ennreal.tendsto_tsum_compl_at_top_zero -> ENNReal.tendsto_tsum_compl_atTop_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Tendsto.{u1, 0} (Finset.{u1} α) ENNReal (fun (s : Finset.{u1} α) => tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (fun (b : Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) α (coeSubtype.{succ u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)))))) b))) (Filter.atTop.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Tendsto.{u1, 0} (Finset.{u1} α) ENNReal (fun (s : Finset.{u1} α) => tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Subtype.{succ u1} α (fun (x : α) => Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s))) (fun (b : Subtype.{succ u1} α (fun (x : α) => Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s))) => f (Subtype.val.{succ u1} α (fun (x : α) => Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s)) b))) (Filter.atTop.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_tsum_compl_at_top_zero ENNReal.tendsto_tsum_compl_atTop_zeroₓ'. -/
/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_atTop_zero {α : Type _} {f : α → ℝ≥0∞} (hf : (∑' x, f x) ≠ ∞) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) :=
  by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
  convert ENNReal.tendsto_coe.2 (NNReal.tendsto_tsum_compl_atTop_zero f)
  ext1 s
  rw [ENNReal.coe_tsum]
  exact NNReal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective
#align ennreal.tendsto_tsum_compl_at_top_zero ENNReal.tendsto_tsum_compl_atTop_zero

/- warning: ennreal.tsum_apply -> ENNReal.tsum_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {f : ι -> α -> ENNReal} {x : α}, Eq.{1} ENNReal (tsum.{u2, u1} (α -> ENNReal) (Pi.addCommMonoid.{u2, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (Pi.topologicalSpace.{u2, 0} α (fun (ᾰ : α) => ENNReal) (fun (a : α) => ENNReal.topologicalSpace)) ι (fun (i : ι) => f i) x) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => f i x))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {f : ι -> α -> ENNReal} {x : α}, Eq.{1} ENNReal (tsum.{u1, u2} (α -> ENNReal) (Pi.addCommMonoid.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal))) (Pi.topologicalSpace.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (a : α) => ENNReal.instTopologicalSpaceENNReal)) ι (fun (i : ι) => f i) x) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => f i x))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_apply ENNReal.tsum_applyₓ'. -/
protected theorem tsum_apply {ι α : Type _} {f : ι → α → ℝ≥0∞} {x : α} :
    (∑' i, f i) x = ∑' i, f i x :=
  tsum_apply <| Pi.summable.mpr fun _ => ENNReal.summable
#align ennreal.tsum_apply ENNReal.tsum_apply

/- warning: ennreal.tsum_sub -> ENNReal.tsum_sub is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> ENNReal} {g : Nat -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => g i)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} (Nat -> ENNReal) (Pi.hasLe.{0, 0} Nat (fun (ᾰ : Nat) => ENNReal) (fun (i : Nat) => Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) g f) -> (Eq.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (f i) (g i))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => f i)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => g i))))
but is expected to have type
  forall {f : Nat -> ENNReal} {g : Nat -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => g i)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} (Nat -> ENNReal) (Pi.hasLe.{0, 0} Nat (fun (ᾰ : Nat) => ENNReal) (fun (i : Nat) => Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) g f) -> (Eq.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (f i) (g i))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => f i)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => g i))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_sub ENNReal.tsum_subₓ'. -/
theorem tsum_sub {f : ℕ → ℝ≥0∞} {g : ℕ → ℝ≥0∞} (h₁ : (∑' i, g i) ≠ ∞) (h₂ : g ≤ f) :
    (∑' i, f i - g i) = (∑' i, f i) - ∑' i, g i :=
  by
  have h₃ : (∑' i, f i - g i) = (∑' i, f i - g i + g i) - ∑' i, g i := by
    rw [ENNReal.tsum_add, ENNReal.add_sub_cancel_right h₁]
  have h₄ : (fun i => f i - g i + g i) = f := by
    ext n
    rw [tsub_add_cancel_of_le (h₂ n)]
  rw [h₄] at h₃
  apply h₃
#align ennreal.tsum_sub ENNReal.tsum_sub

/- warning: ennreal.tsum_mono_subtype -> ENNReal.tsum_mono_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : α -> ENNReal) {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t))))) x))))
but is expected to have type
  forall {α : Type.{u1}} (f : α -> ENNReal) {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} α s) (fun (x : Set.Elem.{u1} α s) => f (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} α t) (fun (x : Set.Elem.{u1} α t) => f (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) x))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_mono_subtype ENNReal.tsum_mono_subtypeₓ'. -/
theorem tsum_mono_subtype (f : α → ℝ≥0∞) {s t : Set α} (h : s ⊆ t) :
    (∑' x : s, f x) ≤ ∑' x : t, f x :=
  by
  simp only [tsum_subtype]
  apply ENNReal.tsum_le_tsum
  exact indicator_le_indicator_of_subset h fun _ => zero_le _
#align ennreal.tsum_mono_subtype ENNReal.tsum_mono_subtype

/- warning: ennreal.tsum_union_le -> ENNReal.tsum_union_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : α -> ENNReal) (s : Set.{u1} α) (t : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)))))) x))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t))))) x))))
but is expected to have type
  forall {α : Type.{u1}} (f : α -> ENNReal) (s : Set.{u1} α) (t : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (fun (x : Set.Elem.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) => f (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) x))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} α s) (fun (x : Set.Elem.{u1} α s) => f (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} α t) (fun (x : Set.Elem.{u1} α t) => f (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) x))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_union_le ENNReal.tsum_union_leₓ'. -/
theorem tsum_union_le (f : α → ℝ≥0∞) (s t : Set α) :
    (∑' x : s ∪ t, f x) ≤ (∑' x : s, f x) + ∑' x : t, f x :=
  calc
    (∑' x : s ∪ t, f x) = ∑' x : s ∪ t \ s, f x :=
      by
      apply tsum_congr_subtype
      rw [union_diff_self]
    _ = (∑' x : s, f x) + ∑' x : t \ s, f x :=
      (tsum_union_disjoint disjoint_sdiff_self_right ENNReal.summable ENNReal.summable)
    _ ≤ (∑' x : s, f x) + ∑' x : t, f x := add_le_add le_rfl (tsum_mono_subtype _ (diff_subset _ _))
    
#align ennreal.tsum_union_le ENNReal.tsum_union_le

/- warning: ennreal.tsum_bUnion_le -> ENNReal.tsum_biUnion_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (f : α -> ENNReal) (s : Finset.{u2} ι) (t : ι -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => t i)))) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => t i)))) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => t i)))) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => t i)))) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => t i)))) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => t i)))) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => t i)))))))) x))) (Finset.sum.{0, u2} ENNReal ι (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (i : ι) => tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (t i)))))) x))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} (f : α -> ENNReal) (s : Finset.{u2} ι) (t : ι -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} α (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) => t i)))) (fun (x : Set.Elem.{u1} α (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) => t i)))) => f (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (fun (h._@.Mathlib.Topology.Instances.ENNReal._hyg.21608 : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) => t i)))) x))) (Finset.sum.{0, u2} ENNReal ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (i : ι) => tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} α (t i)) (fun (x : Set.Elem.{u1} α (t i)) => f (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (t i)) x))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_bUnion_le ENNReal.tsum_biUnion_leₓ'. -/
theorem tsum_biUnion_le {ι : Type _} (f : α → ℝ≥0∞) (s : Finset ι) (t : ι → Set α) :
    (∑' x : ⋃ i ∈ s, t i, f x) ≤ ∑ i in s, ∑' x : t i, f x := by
  classical
    induction' s using Finset.induction_on with i s hi ihs h
    · simp
    have : (⋃ j ∈ insert i s, t j) = t i ∪ ⋃ j ∈ s, t j := by simp
    rw [tsum_congr_subtype f this]
    calc
      (∑' x : t i ∪ ⋃ j ∈ s, t j, f x) ≤ (∑' x : t i, f x) + ∑' x : ⋃ j ∈ s, t j, f x :=
        tsum_union_le _ _ _
      _ ≤ (∑' x : t i, f x) + ∑ i in s, ∑' x : t i, f x := (add_le_add le_rfl ihs)
      _ = ∑ j in insert i s, ∑' x : t j, f x := (Finset.sum_insert hi).symm
      
#align ennreal.tsum_bUnion_le ENNReal.tsum_biUnion_le

/- warning: ennreal.tsum_Union_le -> ENNReal.tsum_iUnion_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Fintype.{u2} ι] (f : α -> ENNReal) (t : ι -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => t i))) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => t i))) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => t i))) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => t i))) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => t i))) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => t i))) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => t i))))))) x))) (Finset.sum.{0, u2} ENNReal ι (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.univ.{u2} ι _inst_1) (fun (i : ι) => tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (t i)))))) x))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Fintype.{u2} ι] (f : α -> ENNReal) (t : ι -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} α (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => t i))) (fun (x : Set.Elem.{u1} α (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => t i))) => f (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => t i))) x))) (Finset.sum.{0, u2} ENNReal ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.univ.{u2} ι _inst_1) (fun (i : ι) => tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} α (t i)) (fun (x : Set.Elem.{u1} α (t i)) => f (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (t i)) x))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_Union_le ENNReal.tsum_iUnion_leₓ'. -/
theorem tsum_iUnion_le {ι : Type _} [Fintype ι] (f : α → ℝ≥0∞) (t : ι → Set α) :
    (∑' x : ⋃ i, t i, f x) ≤ ∑ i, ∑' x : t i, f x := by
  classical
    have : (⋃ i, t i) = ⋃ i ∈ (Finset.univ : Finset ι), t i := by simp
    rw [tsum_congr_subtype f this]
    exact tsum_bUnion_le _ _ _
#align ennreal.tsum_Union_le ENNReal.tsum_iUnion_le

/- warning: ennreal.tsum_eq_add_tsum_ite -> ENNReal.tsum_eq_add_tsum_ite is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {f : β -> ENNReal} (b : β), Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (x : β) => f x)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f b) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (x : β) => ite.{1} ENNReal (Eq.{succ u1} β x b) (Classical.propDecidable (Eq.{succ u1} β x b)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (f x))))
but is expected to have type
  forall {β : Type.{u1}} {f : β -> ENNReal} (b : β), Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (x : β) => f x)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f b) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (x : β) => ite.{1} ENNReal (Eq.{succ u1} β x b) (Classical.propDecidable (Eq.{succ u1} β x b)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (f x))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_eq_add_tsum_ite ENNReal.tsum_eq_add_tsum_iteₓ'. -/
theorem tsum_eq_add_tsum_ite {f : β → ℝ≥0∞} (b : β) :
    (∑' x, f x) = f b + ∑' x, ite (x = b) 0 (f x) :=
  tsum_eq_add_tsum_ite' b ENNReal.summable
#align ennreal.tsum_eq_add_tsum_ite ENNReal.tsum_eq_add_tsum_ite

/- warning: ennreal.tsum_add_one_eq_top -> ENNReal.tsum_add_one_eq_top is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> ENNReal}, (Eq.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => f n)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Ne.{1} ENNReal (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {f : Nat -> ENNReal}, (Eq.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => f n)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Ne.{1} ENNReal (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_add_one_eq_top ENNReal.tsum_add_one_eq_topₓ'. -/
theorem tsum_add_one_eq_top {f : ℕ → ℝ≥0∞} (hf : (∑' n, f n) = ∞) (hf0 : f 0 ≠ ∞) :
    (∑' n, f (n + 1)) = ∞ :=
  by
  rw [← tsum_eq_tsum_of_hasSum_iff_hasSum fun _ => (notMemRangeEquiv 1).hasSum_iff]
  swap
  · infer_instance
  have h₁ :
    ((∑' b : { n // n ∈ Finset.range 1 }, f b) + ∑' b : { n // n ∉ Finset.range 1 }, f b) =
      ∑' b, f b :=
    tsum_add_tsum_compl ENNReal.summable ENNReal.summable
  rw [Finset.tsum_subtype, Finset.sum_range_one, hf, ENNReal.add_eq_top] at h₁
  rw [← h₁.resolve_left hf0]
  apply tsum_congr
  rintro ⟨i, hi⟩
  simp only [Multiset.mem_range, not_lt] at hi
  simp only [tsub_add_cancel_of_le hi, coe_notMemRangeEquiv, Function.comp_apply, Subtype.coe_mk]
#align ennreal.tsum_add_one_eq_top ENNReal.tsum_add_one_eq_top

/- warning: ennreal.finite_const_le_of_tsum_ne_top -> ENNReal.finite_const_le_of_tsum_ne_top is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {a : ι -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => a i)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (a i)))))
but is expected to have type
  forall {ι : Type.{u1}} {a : ι -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => a i)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (a i)))))
Case conversion may be inaccurate. Consider using '#align ennreal.finite_const_le_of_tsum_ne_top ENNReal.finite_const_le_of_tsum_ne_topₓ'. -/
/-- A sum of extended nonnegative reals which is finite can have only finitely many terms
above any positive threshold.-/
theorem finite_const_le_of_tsum_ne_top {ι : Type _} {a : ι → ℝ≥0∞} (tsum_ne_top : (∑' i, a i) ≠ ∞)
    {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) : { i : ι | ε ≤ a i }.Finite :=
  by
  by_cases ε_infty : ε = ∞
  · rw [ε_infty]
    by_contra maybe_infinite
    obtain ⟨j, hj⟩ := Set.Infinite.nonempty maybe_infinite
    exact tsum_ne_top (le_antisymm le_top (le_trans hj (le_tsum' (@ENNReal.summable _ a) j)))
  have key :=
    (nnreal.summable_coe.mpr (summable_to_nnreal_of_tsum_ne_top tsum_ne_top)).tendsto_cofinite_zero
      (Iio_mem_nhds (to_real_pos ε_ne_zero ε_infty))
  simp only [Filter.mem_map, Filter.mem_cofinite, preimage] at key
  have obs : { i : ι | ↑(a i).toNNReal ∈ Iio ε.to_real }ᶜ = { i : ι | ε ≤ a i } :=
    by
    ext i
    simpa only [mem_Iio, mem_compl_iff, mem_set_of_eq, not_lt] using
      to_real_le_to_real ε_infty (ENNReal.ne_top_of_tsum_ne_top tsum_ne_top _)
  rwa [obs] at key
#align ennreal.finite_const_le_of_tsum_ne_top ENNReal.finite_const_le_of_tsum_ne_top

/- warning: ennreal.finset_card_const_le_le_of_tsum_le -> ENNReal.finset_card_const_le_le_of_tsum_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {a : ι -> ENNReal} {c : ENNReal}, (Ne.{1} ENNReal c (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => a i)) c) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{0} (Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (a i)))) (fun (hf : Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (a i)))) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENNReal (HasLiftT.mk.{1, 1} Nat ENNReal (CoeTCₓ.coe.{1, 1} Nat ENNReal (Nat.castCoe.{0} ENNReal (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (Finset.card.{u1} ι (Set.Finite.toFinset.{u1} ι (setOf.{u1} ι (fun (i : ι) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (a i))) hf))) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) c ε))))
but is expected to have type
  forall {ι : Type.{u1}} {a : ι -> ENNReal} {c : ENNReal}, (Ne.{1} ENNReal c (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => a i)) c) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{0} (Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (a i)))) (fun (hf : Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (a i)))) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Nat.cast.{0} ENNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (Finset.card.{u1} ι (Set.Finite.toFinset.{u1} ι (setOf.{u1} ι (fun (i : ι) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (a i))) hf))) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) c ε))))
Case conversion may be inaccurate. Consider using '#align ennreal.finset_card_const_le_le_of_tsum_le ENNReal.finset_card_const_le_le_of_tsum_leₓ'. -/
/-- Markov's inequality for `finset.card` and `tsum` in `ℝ≥0∞`. -/
theorem finset_card_const_le_le_of_tsum_le {ι : Type _} {a : ι → ℝ≥0∞} {c : ℝ≥0∞} (c_ne_top : c ≠ ∞)
    (tsum_le_c : (∑' i, a i) ≤ c) {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) :
    ∃ hf : { i : ι | ε ≤ a i }.Finite, ↑hf.toFinset.card ≤ c / ε :=
  by
  by_cases ε = ∞
  · have obs : { i : ι | ε ≤ a i } = ∅ :=
      by
      rw [eq_empty_iff_forall_not_mem]
      intro i hi
      have oops := (le_trans hi (le_tsum' (@ENNReal.summable _ a) i)).trans tsum_le_c
      rw [h] at oops
      exact c_ne_top (le_antisymm le_top oops)
    simp only [obs, finite_empty, finite.to_finset_empty, Finset.card_empty, algebraMap.coe_zero,
      zero_le', exists_true_left]
  have hf : { i : ι | ε ≤ a i }.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top (lt_of_le_of_lt tsum_le_c c_ne_top.lt_top).Ne ε_ne_zero
  use hf
  have at_least : ∀ i ∈ hf.to_finset, ε ≤ a i :=
    by
    intro i hi
    simpa only [finite.mem_to_finset, mem_set_of_eq] using hi
  have partial_sum :=
    @sum_le_tsum _ _ _ _ _ a hf.to_finset (fun _ _ => zero_le') (@ENNReal.summable _ a)
  have lower_bound := Finset.sum_le_sum at_least
  simp only [Finset.sum_const, nsmul_eq_mul] at lower_bound
  have key := (ENNReal.le_div_iff_mul_le (Or.inl ε_ne_zero) (Or.inl h)).mpr lower_bound
  exact le_trans key (ENNReal.div_le_div_right (partial_sum.trans tsum_le_c) _)
#align ennreal.finset_card_const_le_le_of_tsum_le ENNReal.finset_card_const_le_le_of_tsum_le

end tsum

/- warning: ennreal.tendsto_to_real_iff -> ENNReal.tendsto_toReal_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {fi : Filter.{u1} ι} {f : ι -> ENNReal}, (forall (i : ι), Ne.{1} ENNReal (f i) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {x : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Iff (Filter.Tendsto.{u1, 0} ι Real (fun (n : ι) => ENNReal.toReal (f n)) fi (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (ENNReal.toReal x))) (Filter.Tendsto.{u1, 0} ι ENNReal f fi (nhds.{0} ENNReal ENNReal.topologicalSpace x))))
but is expected to have type
  forall {ι : Type.{u1}} {fi : Filter.{u1} ι} {f : ι -> ENNReal}, (forall (i : ι), Ne.{1} ENNReal (f i) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {x : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Iff (Filter.Tendsto.{u1, 0} ι Real (fun (n : ι) => ENNReal.toReal (f n)) fi (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (ENNReal.toReal x))) (Filter.Tendsto.{u1, 0} ι ENNReal f fi (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal x))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_to_real_iff ENNReal.tendsto_toReal_iffₓ'. -/
theorem tendsto_toReal_iff {ι} {fi : Filter ι} {f : ι → ℝ≥0∞} (hf : ∀ i, f i ≠ ∞) {x : ℝ≥0∞}
    (hx : x ≠ ∞) : fi.Tendsto (fun n => (f n).toReal) (𝓝 x.toReal) ↔ fi.Tendsto f (𝓝 x) :=
  by
  refine' ⟨fun h => _, fun h => tendsto.comp (ENNReal.tendsto_toReal hx) h⟩
  have h_eq : f = fun n => ENNReal.ofReal (f n).toReal :=
    by
    ext1 n
    rw [ENNReal.ofReal_toReal (hf n)]
  rw [h_eq, ← ENNReal.ofReal_toReal hx]
  exact ENNReal.tendsto_ofReal h
#align ennreal.tendsto_to_real_iff ENNReal.tendsto_toReal_iff

/- warning: ennreal.tsum_coe_ne_top_iff_summable_coe -> ENNReal.tsum_coe_ne_top_iff_summable_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal}, Iff (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f a))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Summable.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (f a)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal}, Iff (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => ENNReal.some (f a))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Summable.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : α) => NNReal.toReal (f a)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_coe_ne_top_iff_summable_coe ENNReal.tsum_coe_ne_top_iff_summable_coeₓ'. -/
theorem tsum_coe_ne_top_iff_summable_coe {f : α → ℝ≥0} :
    (∑' a, (f a : ℝ≥0∞)) ≠ ∞ ↔ Summable fun a => (f a : ℝ) :=
  by
  rw [NNReal.summable_coe]
  exact tsum_coe_ne_top_iff_summable
#align ennreal.tsum_coe_ne_top_iff_summable_coe ENNReal.tsum_coe_ne_top_iff_summable_coe

/- warning: ennreal.tsum_coe_eq_top_iff_not_summable_coe -> ENNReal.tsum_coe_eq_top_iff_not_summable_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal}, Iff (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f a))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Not (Summable.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (f a))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal}, Iff (Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => ENNReal.some (f a))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Not (Summable.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : α) => NNReal.toReal (f a))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_coe_eq_top_iff_not_summable_coe ENNReal.tsum_coe_eq_top_iff_not_summable_coeₓ'. -/
theorem tsum_coe_eq_top_iff_not_summable_coe {f : α → ℝ≥0} :
    (∑' a, (f a : ℝ≥0∞)) = ∞ ↔ ¬Summable fun a => (f a : ℝ) :=
  by
  rw [← @Classical.not_not ((∑' a, ↑(f a)) = ⊤)]
  exact not_congr tsum_coe_ne_top_iff_summable_coe
#align ennreal.tsum_coe_eq_top_iff_not_summable_coe ENNReal.tsum_coe_eq_top_iff_not_summable_coe

/- warning: ennreal.has_sum_to_real -> ENNReal.hasSum_toReal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (HasSum.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => ENNReal.toReal (f x)) (tsum.{0, u1} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (x : α) => ENNReal.toReal (f x))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (HasSum.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => ENNReal.toReal (f x)) (tsum.{0, u1} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (x : α) => ENNReal.toReal (f x))))
Case conversion may be inaccurate. Consider using '#align ennreal.has_sum_to_real ENNReal.hasSum_toRealₓ'. -/
theorem hasSum_toReal {f : α → ℝ≥0∞} (hsum : (∑' x, f x) ≠ ∞) :
    HasSum (fun x => (f x).toReal) (∑' x, (f x).toReal) :=
  by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hsum
  simp only [coe_to_real, ← NNReal.coe_tsum, NNReal.hasSum_coe]
  exact (tsum_coe_ne_top_iff_summable.1 hsum).HasSum
#align ennreal.has_sum_to_real ENNReal.hasSum_toReal

/- warning: ennreal.summable_to_real -> ENNReal.summable_toReal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Summable.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => ENNReal.toReal (f x)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Summable.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => ENNReal.toReal (f x)))
Case conversion may be inaccurate. Consider using '#align ennreal.summable_to_real ENNReal.summable_toRealₓ'. -/
theorem summable_toReal {f : α → ℝ≥0∞} (hsum : (∑' x, f x) ≠ ∞) : Summable fun x => (f x).toReal :=
  (hasSum_toReal hsum).Summable
#align ennreal.summable_to_real ENNReal.summable_toReal

end ENNReal

namespace NNReal

open NNReal

/- warning: nnreal.tsum_eq_to_nnreal_tsum -> NNReal.tsum_eq_toNNReal_tsum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {f : β -> NNReal}, Eq.{1} NNReal (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace β (fun (b : β) => f b)) (ENNReal.toNNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (b : β) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f b))))
but is expected to have type
  forall {β : Type.{u1}} {f : β -> NNReal}, Eq.{1} NNReal (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal β (fun (b : β) => f b)) (ENNReal.toNNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (b : β) => ENNReal.some (f b))))
Case conversion may be inaccurate. Consider using '#align nnreal.tsum_eq_to_nnreal_tsum NNReal.tsum_eq_toNNReal_tsumₓ'. -/
theorem tsum_eq_toNNReal_tsum {f : β → ℝ≥0} : (∑' b, f b) = (∑' b, (f b : ℝ≥0∞)).toNNReal :=
  by
  by_cases h : Summable f
  · rw [← ENNReal.coe_tsum h, ENNReal.toNNReal_coe]
  · have A := tsum_eq_zero_of_not_summable h
    simp only [← ENNReal.tsum_coe_ne_top_iff_summable, Classical.not_not] at h
    simp only [h, ENNReal.top_toNNReal, A]
#align nnreal.tsum_eq_to_nnreal_tsum NNReal.tsum_eq_toNNReal_tsum

/- warning: nnreal.exists_le_has_sum_of_le -> NNReal.exists_le_hasSum_of_le is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {f : β -> NNReal} {g : β -> NNReal} {r : NNReal}, (forall (b : β), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (g b) (f b)) -> (HasSum.{0, u1} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f r) -> (Exists.{1} NNReal (fun (p : NNReal) => Exists.{0} (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) p r) (fun (H : LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) p r) => HasSum.{0, u1} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace g p)))
but is expected to have type
  forall {β : Type.{u1}} {f : β -> NNReal} {g : β -> NNReal} {r : NNReal}, (forall (b : β), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (g b) (f b)) -> (HasSum.{0, u1} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f r) -> (Exists.{1} NNReal (fun (p : NNReal) => And (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) p r) (HasSum.{0, u1} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal g p)))
Case conversion may be inaccurate. Consider using '#align nnreal.exists_le_has_sum_of_le NNReal.exists_le_hasSum_of_leₓ'. -/
/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem exists_le_hasSum_of_le {f g : β → ℝ≥0} {r : ℝ≥0} (hgf : ∀ b, g b ≤ f b) (hfr : HasSum f r) :
    ∃ p ≤ r, HasSum g p :=
  have : (∑' b, (g b : ℝ≥0∞)) ≤ r :=
    by
    refine' hasSum_le (fun b => _) ennreal.summable.has_sum (ENNReal.hasSum_coe.2 hfr)
    exact ENNReal.coe_le_coe.2 (hgf _)
  let ⟨p, Eq, hpr⟩ := ENNReal.le_coe_iff.1 this
  ⟨p, hpr, ENNReal.hasSum_coe.1 <| Eq ▸ ENNReal.summable.HasSum⟩
#align nnreal.exists_le_has_sum_of_le NNReal.exists_le_hasSum_of_le

/- warning: nnreal.summable_of_le -> NNReal.summable_of_le is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {f : β -> NNReal} {g : β -> NNReal}, (forall (b : β), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (g b) (f b)) -> (Summable.{0, u1} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) -> (Summable.{0, u1} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace g)
but is expected to have type
  forall {β : Type.{u1}} {f : β -> NNReal} {g : β -> NNReal}, (forall (b : β), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (g b) (f b)) -> (Summable.{0, u1} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) -> (Summable.{0, u1} NNReal β (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal g)
Case conversion may be inaccurate. Consider using '#align nnreal.summable_of_le NNReal.summable_of_leₓ'. -/
/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem summable_of_le {f g : β → ℝ≥0} (hgf : ∀ b, g b ≤ f b) : Summable f → Summable g
  | ⟨r, hfr⟩ =>
    let ⟨p, _, hp⟩ := exists_le_hasSum_of_le hgf hfr
    hp.Summable
#align nnreal.summable_of_le NNReal.summable_of_le

/- warning: nnreal.has_sum_iff_tendsto_nat -> NNReal.hasSum_iff_tendsto_nat is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> NNReal} {r : NNReal}, Iff (HasSum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f r) (Filter.Tendsto.{0, 0} Nat NNReal (fun (n : Nat) => Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} NNReal NNReal.topologicalSpace r))
but is expected to have type
  forall {f : Nat -> NNReal} {r : NNReal}, Iff (HasSum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f r) (Filter.Tendsto.{0, 0} Nat NNReal (fun (n : Nat) => Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal r))
Case conversion may be inaccurate. Consider using '#align nnreal.has_sum_iff_tendsto_nat NNReal.hasSum_iff_tendsto_natₓ'. -/
/-- A series of non-negative real numbers converges to `r` in the sense of `has_sum` if and only if
the sequence of partial sum converges to `r`. -/
theorem hasSum_iff_tendsto_nat {f : ℕ → ℝ≥0} {r : ℝ≥0} :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop (𝓝 r) :=
  by
  rw [← ENNReal.hasSum_coe, ENNReal.hasSum_iff_tendsto_nat]
  simp only [ennreal.coe_finset_sum.symm]
  exact ENNReal.tendsto_coe
#align nnreal.has_sum_iff_tendsto_nat NNReal.hasSum_iff_tendsto_nat

/- warning: nnreal.not_summable_iff_tendsto_nat_at_top -> NNReal.not_summable_iff_tendsto_nat_atTop is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> NNReal}, Iff (Not (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f)) (Filter.Tendsto.{0, 0} Nat NNReal (fun (n : Nat) => Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))
but is expected to have type
  forall {f : Nat -> NNReal}, Iff (Not (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f)) (Filter.Tendsto.{0, 0} Nat NNReal (fun (n : Nat) => Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))))
Case conversion may be inaccurate. Consider using '#align nnreal.not_summable_iff_tendsto_nat_at_top NNReal.not_summable_iff_tendsto_nat_atTopₓ'. -/
theorem not_summable_iff_tendsto_nat_atTop {f : ℕ → ℝ≥0} :
    ¬Summable f ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop atTop :=
  by
  constructor
  · intro h
    refine' ((tendsto_of_monotone _).resolve_right h).comp _
    exacts[Finset.sum_mono_set _, tendsto_finset_range]
  · rintro hnat ⟨r, hr⟩
    exact not_tendsto_nhds_of_tendsto_atTop hnat _ (has_sum_iff_tendsto_nat.1 hr)
#align nnreal.not_summable_iff_tendsto_nat_at_top NNReal.not_summable_iff_tendsto_nat_atTop

/- warning: nnreal.summable_iff_not_tendsto_nat_at_top -> NNReal.summable_iff_not_tendsto_nat_atTop is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> NNReal}, Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) (Not (Filter.Tendsto.{0, 0} Nat NNReal (fun (n : Nat) => Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))))
but is expected to have type
  forall {f : Nat -> NNReal}, Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) (Not (Filter.Tendsto.{0, 0} Nat NNReal (fun (n : Nat) => Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)))))
Case conversion may be inaccurate. Consider using '#align nnreal.summable_iff_not_tendsto_nat_at_top NNReal.summable_iff_not_tendsto_nat_atTopₓ'. -/
theorem summable_iff_not_tendsto_nat_atTop {f : ℕ → ℝ≥0} :
    Summable f ↔ ¬Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not, Classical.not_not, not_summable_iff_tendsto_nat_at_top]
#align nnreal.summable_iff_not_tendsto_nat_at_top NNReal.summable_iff_not_tendsto_nat_atTop

/- warning: nnreal.summable_of_sum_range_le -> NNReal.summable_of_sum_range_le is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> NNReal} {c : NNReal}, (forall (n : Nat), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) (Finset.range n) (fun (i : Nat) => f i)) c) -> (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f)
but is expected to have type
  forall {f : Nat -> NNReal} {c : NNReal}, (forall (n : Nat), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) (Finset.range n) (fun (i : Nat) => f i)) c) -> (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f)
Case conversion may be inaccurate. Consider using '#align nnreal.summable_of_sum_range_le NNReal.summable_of_sum_range_leₓ'. -/
theorem summable_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
    (h : ∀ n, (∑ i in Finset.range n, f i) ≤ c) : Summable f :=
  by
  apply summable_iff_not_tendsto_nat_at_top.2 fun H => _
  rcases exists_lt_of_tendsto_at_top H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))
#align nnreal.summable_of_sum_range_le NNReal.summable_of_sum_range_le

/- warning: nnreal.tsum_le_of_sum_range_le -> NNReal.tsum_le_of_sum_range_le is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> NNReal} {c : NNReal}, (forall (n : Nat), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) (Finset.range n) (fun (i : Nat) => f i)) c) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (tsum.{0, 0} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace Nat (fun (n : Nat) => f n)) c)
but is expected to have type
  forall {f : Nat -> NNReal} {c : NNReal}, (forall (n : Nat), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Finset.sum.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) (Finset.range n) (fun (i : Nat) => f i)) c) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (tsum.{0, 0} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal Nat (fun (n : Nat) => f n)) c)
Case conversion may be inaccurate. Consider using '#align nnreal.tsum_le_of_sum_range_le NNReal.tsum_le_of_sum_range_leₓ'. -/
theorem tsum_le_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
    (h : ∀ n, (∑ i in Finset.range n, f i) ≤ c) : (∑' n, f n) ≤ c :=
  tsum_le_of_sum_range_le (summable_of_sum_range_le h) h
#align nnreal.tsum_le_of_sum_range_le NNReal.tsum_le_of_sum_range_le

/- warning: nnreal.tsum_comp_le_tsum_of_inj -> NNReal.tsum_comp_le_tsum_of_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) -> (forall {i : β -> α}, (Function.Injective.{succ u2, succ u1} β α i) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (tsum.{0, u2} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace β (fun (x : β) => f (i x))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (x : α) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) -> (forall {i : β -> α}, (Function.Injective.{succ u2, succ u1} β α i) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (tsum.{0, u2} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal β (fun (x : β) => f (i x))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (x : α) => f x))))
Case conversion may be inaccurate. Consider using '#align nnreal.tsum_comp_le_tsum_of_inj NNReal.tsum_comp_le_tsum_of_injₓ'. -/
theorem tsum_comp_le_tsum_of_inj {β : Type _} {f : α → ℝ≥0} (hf : Summable f) {i : β → α}
    (hi : Function.Injective i) : (∑' x, f (i x)) ≤ ∑' x, f x :=
  tsum_le_tsum_of_inj i hi (fun c hc => zero_le _) (fun b => le_rfl) (summable_comp_injective hf hi)
    hf
#align nnreal.tsum_comp_le_tsum_of_inj NNReal.tsum_comp_le_tsum_of_inj

/- warning: nnreal.summable_sigma -> NNReal.summable_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {f : (Sigma.{u1, u2} α (fun (x : α) => β x)) -> NNReal}, Iff (Summable.{0, max u1 u2} NNReal (Sigma.{u1, u2} α (fun (x : α) => β x)) (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) (And (forall (x : α), Summable.{0, u2} NNReal (β x) (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (y : β x) => f (Sigma.mk.{u1, u2} α (fun (x : α) => β x) x y))) (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (x : α) => tsum.{0, u2} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (β x) (fun (y : β x) => f (Sigma.mk.{u1, u2} α (fun (x : α) => β x) x y)))))
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {f : (Sigma.{u1, u2} α (fun (x : α) => β x)) -> NNReal}, Iff (Summable.{0, max u1 u2} NNReal (Sigma.{u1, u2} α (fun (x : α) => β x)) (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) (And (forall (x : α), Summable.{0, u2} NNReal (β x) (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (y : β x) => f (Sigma.mk.{u1, u2} α (fun (x : α) => β x) x y))) (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (x : α) => tsum.{0, u2} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (β x) (fun (y : β x) => f (Sigma.mk.{u1, u2} α (fun (x : α) => β x) x y)))))
Case conversion may be inaccurate. Consider using '#align nnreal.summable_sigma NNReal.summable_sigmaₓ'. -/
theorem summable_sigma {β : ∀ x : α, Type _} {f : (Σx, β x) → ℝ≥0} :
    Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ :=
  by
  constructor
  · simp only [← NNReal.summable_coe, NNReal.coe_tsum]
    exact fun h => ⟨h.sigma_factor, h.Sigma⟩
  · rintro ⟨h₁, h₂⟩
    simpa only [← ENNReal.tsum_coe_ne_top_iff_summable, ENNReal.tsum_sigma', ENNReal.coe_tsum,
      h₁] using h₂
#align nnreal.summable_sigma NNReal.summable_sigma

/- warning: nnreal.indicator_summable -> NNReal.indicator_summable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) -> (forall (s : Set.{u1} α), Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (Set.indicator.{u1, 0} α NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) s f))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) -> (forall (s : Set.{u1} α), Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (Set.indicator.{u1, 0} α NNReal instNNRealZero s f))
Case conversion may be inaccurate. Consider using '#align nnreal.indicator_summable NNReal.indicator_summableₓ'. -/
theorem indicator_summable {f : α → ℝ≥0} (hf : Summable f) (s : Set α) : Summable (s.indicator f) :=
  by
  refine' NNReal.summable_of_le (fun a => le_trans (le_of_eq (s.indicator_apply f a)) _) hf
  split_ifs
  exact le_refl (f a)
  exact zero_le_coe
#align nnreal.indicator_summable NNReal.indicator_summable

/- warning: nnreal.tsum_indicator_ne_zero -> NNReal.tsum_indicator_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) -> (forall {s : Set.{u1} α}, (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Ne.{1} NNReal (f a) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))))) -> (Ne.{1} NNReal (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (x : α) => Set.indicator.{u1, 0} α NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) s f x)) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) -> (forall {s : Set.{u1} α}, (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Ne.{1} NNReal (f a) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))))) -> (Ne.{1} NNReal (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (x : α) => Set.indicator.{u1, 0} α NNReal instNNRealZero s f x)) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))))
Case conversion may be inaccurate. Consider using '#align nnreal.tsum_indicator_ne_zero NNReal.tsum_indicator_ne_zeroₓ'. -/
theorem tsum_indicator_ne_zero {f : α → ℝ≥0} (hf : Summable f) {s : Set α} (h : ∃ a ∈ s, f a ≠ 0) :
    (∑' x, (s.indicator f) x) ≠ 0 := fun h' =>
  let ⟨a, ha, hap⟩ := h
  hap
    (trans (Set.indicator_apply_eq_self.mpr (absurd ha)).symm
      (((tsum_eq_zero_iff (indicator_summable hf s)).1 h') a))
#align nnreal.tsum_indicator_ne_zero NNReal.tsum_indicator_ne_zero

open Finset

/- warning: nnreal.tendsto_sum_nat_add -> NNReal.tendsto_sum_nat_add is a dubious translation:
lean 3 declaration is
  forall (f : Nat -> NNReal), Filter.Tendsto.{0, 0} Nat NNReal (fun (i : Nat) => tsum.{0, 0} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace Nat (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} NNReal NNReal.topologicalSpace (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall (f : Nat -> NNReal), Filter.Tendsto.{0, 0} Nat NNReal (fun (i : Nat) => tsum.{0, 0} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal Nat (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)))
Case conversion may be inaccurate. Consider using '#align nnreal.tendsto_sum_nat_add NNReal.tendsto_sum_nat_addₓ'. -/
/-- For `f : ℕ → ℝ≥0`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add (f : ℕ → ℝ≥0) : Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) :=
  by
  rw [← tendsto_coe]
  convert tendsto_sum_nat_add fun i => (f i : ℝ)
  norm_cast
#align nnreal.tendsto_sum_nat_add NNReal.tendsto_sum_nat_add

/- warning: nnreal.has_sum_lt -> NNReal.hasSum_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal} {g : α -> NNReal} {sf : NNReal} {sg : NNReal} {i : α}, (forall (a : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (f a) (g a)) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (f i) (g i)) -> (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f sf) -> (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace g sg) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) sf sg)
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal} {g : α -> NNReal} {sf : NNReal} {sg : NNReal} {i : α}, (forall (a : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (f a) (g a)) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (f i) (g i)) -> (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f sf) -> (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal g sg) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) sf sg)
Case conversion may be inaccurate. Consider using '#align nnreal.has_sum_lt NNReal.hasSum_ltₓ'. -/
theorem hasSum_lt {f g : α → ℝ≥0} {sf sg : ℝ≥0} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg :=
  by
  have A : ∀ a : α, (f a : ℝ) ≤ g a := fun a => NNReal.coe_le_coe.2 (h a)
  have : (sf : ℝ) < sg := hasSum_lt A (NNReal.coe_lt_coe.2 hi) (has_sum_coe.2 hf) (has_sum_coe.2 hg)
  exact NNReal.coe_lt_coe.1 this
#align nnreal.has_sum_lt NNReal.hasSum_lt

/- warning: nnreal.has_sum_strict_mono -> NNReal.hasSum_strict_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal} {g : α -> NNReal} {sf : NNReal} {sg : NNReal}, (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f sf) -> (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace g sg) -> (LT.lt.{u1} (α -> NNReal) (Preorder.toHasLt.{u1} (α -> NNReal) (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) f g) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) sf sg)
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal} {g : α -> NNReal} {sf : NNReal} {sg : NNReal}, (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f sf) -> (HasSum.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal g sg) -> (LT.lt.{u1} (α -> NNReal) (Preorder.toLT.{u1} (α -> NNReal) (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)))) f g) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) sf sg)
Case conversion may be inaccurate. Consider using '#align nnreal.has_sum_strict_mono NNReal.hasSum_strict_monoₓ'. -/
@[mono]
theorem hasSum_strict_mono {f g : α → ℝ≥0} {sf sg : ℝ≥0} (hf : HasSum f sf) (hg : HasSum g sg)
    (h : f < g) : sf < sg :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  hasSum_lt hle hi hf hg
#align nnreal.has_sum_strict_mono NNReal.hasSum_strict_mono

/- warning: nnreal.tsum_lt_tsum -> NNReal.tsum_lt_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal} {g : α -> NNReal} {i : α}, (forall (a : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (f a) (g a)) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (f i) (g i)) -> (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace g) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (n : α) => f n)) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (n : α) => g n)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal} {g : α -> NNReal} {i : α}, (forall (a : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (f a) (g a)) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (f i) (g i)) -> (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal g) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (n : α) => f n)) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (n : α) => g n)))
Case conversion may be inaccurate. Consider using '#align nnreal.tsum_lt_tsum NNReal.tsum_lt_tsumₓ'. -/
theorem tsum_lt_tsum {f g : α → ℝ≥0} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hg : Summable g) : (∑' n, f n) < ∑' n, g n :=
  hasSum_lt h hi (summable_of_le h hg).HasSum hg.HasSum
#align nnreal.tsum_lt_tsum NNReal.tsum_lt_tsum

/- warning: nnreal.tsum_strict_mono -> NNReal.tsum_strict_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal} {g : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace g) -> (LT.lt.{u1} (α -> NNReal) (Preorder.toHasLt.{u1} (α -> NNReal) (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) f g) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (n : α) => f n)) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (n : α) => g n)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal} {g : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal g) -> (LT.lt.{u1} (α -> NNReal) (Preorder.toLT.{u1} (α -> NNReal) (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)))) f g) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (n : α) => f n)) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (n : α) => g n)))
Case conversion may be inaccurate. Consider using '#align nnreal.tsum_strict_mono NNReal.tsum_strict_monoₓ'. -/
@[mono]
theorem tsum_strict_mono {f g : α → ℝ≥0} (hg : Summable g) (h : f < g) : (∑' n, f n) < ∑' n, g n :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hg
#align nnreal.tsum_strict_mono NNReal.tsum_strict_mono

/- warning: nnreal.tsum_pos -> NNReal.tsum_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {g : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace g) -> (forall (i : α), (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (g i)) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (b : α) => g b))))
but is expected to have type
  forall {α : Type.{u1}} {g : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal g) -> (forall (i : α), (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) (g i)) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (b : α) => g b))))
Case conversion may be inaccurate. Consider using '#align nnreal.tsum_pos NNReal.tsum_posₓ'. -/
theorem tsum_pos {g : α → ℝ≥0} (hg : Summable g) (i : α) (hi : 0 < g i) : 0 < ∑' b, g b :=
  by
  rw [← tsum_zero]
  exact tsum_lt_tsum (fun a => zero_le _) hi hg
#align nnreal.tsum_pos NNReal.tsum_pos

/- warning: nnreal.tsum_eq_add_tsum_ite -> NNReal.tsum_eq_add_tsum_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f) -> (forall (i : α), Eq.{1} NNReal (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (x : α) => f x)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (f i) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (x : α) => ite.{1} NNReal (Eq.{succ u1} α x i) (Classical.propDecidable (Eq.{succ u1} α x i)) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (f x)))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal}, (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f) -> (forall (i : α), Eq.{1} NNReal (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (x : α) => f x)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (f i) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (x : α) => ite.{1} NNReal (Eq.{succ u1} α x i) (Classical.propDecidable (Eq.{succ u1} α x i)) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) (f x)))))
Case conversion may be inaccurate. Consider using '#align nnreal.tsum_eq_add_tsum_ite NNReal.tsum_eq_add_tsum_iteₓ'. -/
theorem tsum_eq_add_tsum_ite {f : α → ℝ≥0} (hf : Summable f) (i : α) :
    (∑' x, f x) = f i + ∑' x, ite (x = i) 0 (f x) :=
  by
  refine' tsum_eq_add_tsum_ite' i (NNReal.summable_of_le (fun i' => _) hf)
  rw [Function.update_apply]
  split_ifs <;> simp only [zero_le', le_rfl]
#align nnreal.tsum_eq_add_tsum_ite NNReal.tsum_eq_add_tsum_ite

end NNReal

namespace ENNReal

/- warning: ennreal.tsum_to_nnreal_eq -> ENNReal.tsum_toNNReal_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, (forall (a : α), Ne.{1} ENNReal (f a) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} NNReal (ENNReal.toNNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (a : α) => ENNReal.toNNReal (f a))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, (forall (a : α), Ne.{1} ENNReal (f a) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} NNReal (ENNReal.toNNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (a : α) => ENNReal.toNNReal (f a))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_to_nnreal_eq ENNReal.tsum_toNNReal_eqₓ'. -/
theorem tsum_toNNReal_eq {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
    (∑' a, f a).toNNReal = ∑' a, (f a).toNNReal :=
  (congr_arg ENNReal.toNNReal (tsum_congr fun x => (coe_toNNReal (hf x)).symm)).trans
    NNReal.tsum_eq_toNNReal_tsum.symm
#align ennreal.tsum_to_nnreal_eq ENNReal.tsum_toNNReal_eq

/- warning: ennreal.tsum_to_real_eq -> ENNReal.tsum_toReal_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal}, (forall (a : α), Ne.{1} ENNReal (f a) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} Real (ENNReal.toReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a))) (tsum.{0, u1} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (a : α) => ENNReal.toReal (f a))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal}, (forall (a : α), Ne.{1} ENNReal (f a) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} Real (ENNReal.toReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a))) (tsum.{0, u1} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (a : α) => ENNReal.toReal (f a))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_to_real_eq ENNReal.tsum_toReal_eqₓ'. -/
theorem tsum_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
    (∑' a, f a).toReal = ∑' a, (f a).toReal := by
  simp only [ENNReal.toReal, tsum_to_nnreal_eq hf, NNReal.coe_tsum]
#align ennreal.tsum_to_real_eq ENNReal.tsum_toReal_eq

/- warning: ennreal.tendsto_sum_nat_add -> ENNReal.tendsto_sum_nat_add is a dubious translation:
lean 3 declaration is
  forall (f : Nat -> ENNReal), (Ne.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => f i)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Tendsto.{0, 0} Nat ENNReal (fun (i : Nat) => tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall (f : Nat -> ENNReal), (Ne.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => f i)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Tendsto.{0, 0} Nat ENNReal (fun (i : Nat) => tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_sum_nat_add ENNReal.tendsto_sum_nat_addₓ'. -/
theorem tendsto_sum_nat_add (f : ℕ → ℝ≥0∞) (hf : (∑' i, f i) ≠ ∞) :
    Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) :=
  by
  lift f to ℕ → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
  replace hf : Summable f := tsum_coe_ne_top_iff_summable.1 hf
  simp only [← ENNReal.coe_tsum, NNReal.summable_nat_add _ hf, ← ENNReal.coe_zero]
  exact_mod_cast NNReal.tendsto_sum_nat_add f
#align ennreal.tendsto_sum_nat_add ENNReal.tendsto_sum_nat_add

/- warning: ennreal.tsum_le_of_sum_range_le -> ENNReal.tsum_le_of_sum_range_le is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> ENNReal} {c : ENNReal}, (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.range n) (fun (i : Nat) => f i)) c) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => f n)) c)
but is expected to have type
  forall {f : Nat -> ENNReal} {c : ENNReal}, (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.range n) (fun (i : Nat) => f i)) c) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => f n)) c)
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_le_of_sum_range_le ENNReal.tsum_le_of_sum_range_leₓ'. -/
theorem tsum_le_of_sum_range_le {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ n, (∑ i in Finset.range n, f i) ≤ c) : (∑' n, f n) ≤ c :=
  tsum_le_of_sum_range_le ENNReal.summable h
#align ennreal.tsum_le_of_sum_range_le ENNReal.tsum_le_of_sum_range_le

/- warning: ennreal.has_sum_lt -> ENNReal.hasSum_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} {g : α -> ENNReal} {sf : ENNReal} {sg : ENNReal} {i : α}, (forall (a : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f a) (g a)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f i) (g i)) -> (Ne.{1} ENNReal sf (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (HasSum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace f sf) -> (HasSum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace g sg) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) sf sg)
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} {g : α -> ENNReal} {sf : ENNReal} {sg : ENNReal} {i : α}, (forall (a : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f a) (g a)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f i) (g i)) -> (Ne.{1} ENNReal sf (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (HasSum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal f sf) -> (HasSum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal g sg) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) sf sg)
Case conversion may be inaccurate. Consider using '#align ennreal.has_sum_lt ENNReal.hasSum_ltₓ'. -/
theorem hasSum_lt {f g : α → ℝ≥0∞} {sf sg : ℝ≥0∞} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hsf : sf ≠ ⊤) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg :=
  by
  by_cases hsg : sg = ⊤
  · exact hsg.symm ▸ lt_of_le_of_ne le_top hsf
  · have hg' : ∀ x, g x ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top (hg.tsum_eq.symm ▸ hsg)
    lift f to α → ℝ≥0 using fun x =>
      ne_of_lt (lt_of_le_of_lt (h x) <| lt_of_le_of_ne le_top (hg' x))
    lift g to α → ℝ≥0 using hg'
    lift sf to ℝ≥0 using hsf
    lift sg to ℝ≥0 using hsg
    simp only [coe_le_coe, coe_lt_coe] at h hi⊢
    exact NNReal.hasSum_lt h hi (ENNReal.hasSum_coe.1 hf) (ENNReal.hasSum_coe.1 hg)
#align ennreal.has_sum_lt ENNReal.hasSum_lt

/- warning: ennreal.tsum_lt_tsum -> ENNReal.tsum_lt_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} {g : α -> ENNReal} {i : α}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α f) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall (a : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f a) (g a)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f i) (g i)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => f x)) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => g x)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} {g : α -> ENNReal} {i : α}, (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α f) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall (a : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f a) (g a)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f i) (g i)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => f x)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => g x)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_lt_tsum ENNReal.tsum_lt_tsumₓ'. -/
theorem tsum_lt_tsum {f g : α → ℝ≥0∞} {i : α} (hfi : tsum f ≠ ⊤) (h : ∀ a : α, f a ≤ g a)
    (hi : f i < g i) : (∑' x, f x) < ∑' x, g x :=
  hasSum_lt h hi hfi ENNReal.summable.HasSum ENNReal.summable.HasSum
#align ennreal.tsum_lt_tsum ENNReal.tsum_lt_tsum

end ENNReal

/- warning: tsum_comp_le_tsum_of_inj -> tsum_comp_le_tsum_of_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> Real}, (Summable.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (forall (a : α), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f a)) -> (forall {i : β -> α}, (Function.Injective.{succ u2, succ u1} β α i) -> (LE.le.{0} Real Real.hasLe (tsum.{0, u2} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) β (Function.comp.{succ u2, succ u1, 1} β α Real f i)) (tsum.{0, u1} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> Real}, (Summable.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (forall (a : α), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f a)) -> (forall {i : β -> α}, (Function.Injective.{succ u2, succ u1} β α i) -> (LE.le.{0} Real Real.instLEReal (tsum.{0, u2} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) β (Function.comp.{succ u2, succ u1, 1} β α Real f i)) (tsum.{0, u1} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α f)))
Case conversion may be inaccurate. Consider using '#align tsum_comp_le_tsum_of_inj tsum_comp_le_tsum_of_injₓ'. -/
theorem tsum_comp_le_tsum_of_inj {β : Type _} {f : α → ℝ} (hf : Summable f) (hn : ∀ a, 0 ≤ f a)
    {i : β → α} (hi : Function.Injective i) : tsum (f ∘ i) ≤ tsum f :=
  by
  lift f to α → ℝ≥0 using hn
  rw [NNReal.summable_coe] at hf
  simpa only [(· ∘ ·), ← NNReal.coe_tsum] using NNReal.tsum_comp_le_tsum_of_inj hf hi
#align tsum_comp_le_tsum_of_inj tsum_comp_le_tsum_of_inj

/- warning: summable_of_nonneg_of_le -> summable_of_nonneg_of_le is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {f : β -> Real} {g : β -> Real}, (forall (b : β), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (g b)) -> (forall (b : β), LE.le.{0} Real Real.hasLe (g b) (f b)) -> (Summable.{0, u1} Real β Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Summable.{0, u1} Real β Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g)
but is expected to have type
  forall {β : Type.{u1}} {f : β -> Real} {g : β -> Real}, (forall (b : β), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (g b)) -> (forall (b : β), LE.le.{0} Real Real.instLEReal (g b) (f b)) -> (Summable.{0, u1} Real β Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Summable.{0, u1} Real β Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g)
Case conversion may be inaccurate. Consider using '#align summable_of_nonneg_of_le summable_of_nonneg_of_leₓ'. -/
/-- Comparison test of convergence of series of non-negative real numbers. -/
theorem summable_of_nonneg_of_le {f g : β → ℝ} (hg : ∀ b, 0 ≤ g b) (hgf : ∀ b, g b ≤ f b)
    (hf : Summable f) : Summable g :=
  by
  lift f to β → ℝ≥0 using fun b => (hg b).trans (hgf b)
  lift g to β → ℝ≥0 using hg
  rw [NNReal.summable_coe] at hf⊢
  exact NNReal.summable_of_le (fun b => NNReal.coe_le_coe.1 (hgf b)) hf
#align summable_of_nonneg_of_le summable_of_nonneg_of_le

/- warning: summable.to_nnreal -> Summable.toNNReal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> Real}, (Summable.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (n : α) => Real.toNNReal (f n)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> Real}, (Summable.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (n : α) => Real.toNNReal (f n)))
Case conversion may be inaccurate. Consider using '#align summable.to_nnreal Summable.toNNRealₓ'. -/
theorem Summable.toNNReal {f : α → ℝ} (hf : Summable f) : Summable fun n => (f n).toNNReal :=
  by
  apply NNReal.summable_coe.1
  refine' summable_of_nonneg_of_le (fun n => NNReal.coe_nonneg _) (fun n => _) hf.abs
  simp only [le_abs_self, Real.coe_toNNReal', max_le_iff, abs_nonneg, and_self_iff]
#align summable.to_nnreal Summable.toNNReal

/- warning: has_sum_iff_tendsto_nat_of_nonneg -> hasSum_iff_tendsto_nat_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (forall (i : Nat), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f i)) -> (forall (r : Real), Iff (HasSum.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f r) (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) r)))
but is expected to have type
  forall {f : Nat -> Real}, (forall (i : Nat), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f i)) -> (forall (r : Real), Iff (HasSum.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f r) (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) r)))
Case conversion may be inaccurate. Consider using '#align has_sum_iff_tendsto_nat_of_nonneg hasSum_iff_tendsto_nat_of_nonnegₓ'. -/
/-- A series of non-negative real numbers converges to `r` in the sense of `has_sum` if and only if
the sequence of partial sum converges to `r`. -/
theorem hasSum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (r : ℝ) :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop (𝓝 r) :=
  by
  lift f to ℕ → ℝ≥0 using hf
  simp only [HasSum, ← NNReal.coe_sum, NNReal.tendsto_coe']
  exact exists_congr fun hr => NNReal.hasSum_iff_tendsto_nat
#align has_sum_iff_tendsto_nat_of_nonneg hasSum_iff_tendsto_nat_of_nonneg

/- warning: ennreal.of_real_tsum_of_nonneg -> ENNReal.ofReal_tsum_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> Real}, (forall (n : α), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f n)) -> (Summable.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Eq.{1} ENNReal (ENNReal.ofReal (tsum.{0, u1} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (n : α) => f n))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (n : α) => ENNReal.ofReal (f n))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> Real}, (forall (n : α), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f n)) -> (Summable.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Eq.{1} ENNReal (ENNReal.ofReal (tsum.{0, u1} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) α (fun (n : α) => f n))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (n : α) => ENNReal.ofReal (f n))))
Case conversion may be inaccurate. Consider using '#align ennreal.of_real_tsum_of_nonneg ENNReal.ofReal_tsum_of_nonnegₓ'. -/
theorem ENNReal.ofReal_tsum_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f) :
    ENNReal.ofReal (∑' n, f n) = ∑' n, ENNReal.ofReal (f n) := by
  simp_rw [ENNReal.ofReal, ENNReal.tsum_coe_eq (NNReal.hasSum_real_toNNReal_of_nonneg hf_nonneg hf)]
#align ennreal.of_real_tsum_of_nonneg ENNReal.ofReal_tsum_of_nonneg

/- warning: not_summable_iff_tendsto_nat_at_top_of_nonneg -> not_summable_iff_tendsto_nat_atTop_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (forall (n : Nat), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f n)) -> (Iff (Not (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)) (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (Filter.atTop.{0} Real Real.preorder)))
but is expected to have type
  forall {f : Nat -> Real}, (forall (n : Nat), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f n)) -> (Iff (Not (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)) (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (Filter.atTop.{0} Real Real.instPreorderReal)))
Case conversion may be inaccurate. Consider using '#align not_summable_iff_tendsto_nat_at_top_of_nonneg not_summable_iff_tendsto_nat_atTop_of_nonnegₓ'. -/
theorem not_summable_iff_tendsto_nat_atTop_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    ¬Summable f ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop atTop :=
  by
  lift f to ℕ → ℝ≥0 using hf
  exact_mod_cast NNReal.not_summable_iff_tendsto_nat_atTop
#align not_summable_iff_tendsto_nat_at_top_of_nonneg not_summable_iff_tendsto_nat_atTop_of_nonneg

/- warning: summable_iff_not_tendsto_nat_at_top_of_nonneg -> summable_iff_not_tendsto_nat_atTop_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (forall (n : Nat), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f n)) -> (Iff (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) (Not (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (Filter.atTop.{0} Real Real.preorder))))
but is expected to have type
  forall {f : Nat -> Real}, (forall (n : Nat), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f n)) -> (Iff (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) (Not (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => f i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (Filter.atTop.{0} Real Real.instPreorderReal))))
Case conversion may be inaccurate. Consider using '#align summable_iff_not_tendsto_nat_at_top_of_nonneg summable_iff_not_tendsto_nat_atTop_of_nonnegₓ'. -/
theorem summable_iff_not_tendsto_nat_atTop_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    Summable f ↔ ¬Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not, Classical.not_not, not_summable_iff_tendsto_nat_atTop_of_nonneg hf]
#align summable_iff_not_tendsto_nat_at_top_of_nonneg summable_iff_not_tendsto_nat_atTop_of_nonneg

/- warning: summable_sigma_of_nonneg -> summable_sigma_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {f : (Sigma.{u1, u2} α (fun (x : α) => β x)) -> Real}, (forall (x : Sigma.{u1, u2} α (fun (x : α) => β x)), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f x)) -> (Iff (Summable.{0, max u1 u2} Real (Sigma.{u1, u2} α (fun (x : α) => β x)) Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) (And (forall (x : α), Summable.{0, u2} Real (β x) Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (y : β x) => f (Sigma.mk.{u1, u2} α (fun (x : α) => β x) x y))) (Summable.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => tsum.{0, u2} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (β x) (fun (y : β x) => f (Sigma.mk.{u1, u2} α (fun (x : α) => β x) x y))))))
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {f : (Sigma.{u1, u2} α (fun (x : α) => β x)) -> Real}, (forall (x : Sigma.{u1, u2} α (fun (x : α) => β x)), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f x)) -> (Iff (Summable.{0, max u1 u2} Real (Sigma.{u1, u2} α (fun (x : α) => β x)) Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) (And (forall (x : α), Summable.{0, u2} Real (β x) Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (y : β x) => f (Sigma.mk.{u1, u2} α (fun (x : α) => β x) x y))) (Summable.{0, u1} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => tsum.{0, u2} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (β x) (fun (y : β x) => f (Sigma.mk.{u1, u2} α (fun (x : α) => β x) x y))))))
Case conversion may be inaccurate. Consider using '#align summable_sigma_of_nonneg summable_sigma_of_nonnegₓ'. -/
theorem summable_sigma_of_nonneg {β : ∀ x : α, Type _} {f : (Σx, β x) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ :=
  by
  lift f to (Σx, β x) → ℝ≥0 using hf
  exact_mod_cast NNReal.summable_sigma
#align summable_sigma_of_nonneg summable_sigma_of_nonneg

/- warning: summable_of_sum_le -> summable_of_sum_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {f : ι -> Real} {c : Real}, (LE.le.{u1} (ι -> Real) (Pi.hasLe.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.hasLe)) (OfNat.ofNat.{u1} (ι -> Real) 0 (OfNat.mk.{u1} (ι -> Real) 0 (Zero.zero.{u1} (ι -> Real) (Pi.instZero.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.hasZero))))) f) -> (forall (u : Finset.{u1} ι), LE.le.{0} Real Real.hasLe (Finset.sum.{0, u1} Real ι Real.addCommMonoid u (fun (x : ι) => f x)) c) -> (Summable.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)
but is expected to have type
  forall {ι : Type.{u1}} {f : ι -> Real} {c : Real}, (LE.le.{u1} (ι -> Real) (Pi.hasLe.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.instLEReal)) (OfNat.ofNat.{u1} (ι -> Real) 0 (Zero.toOfNat0.{u1} (ι -> Real) (Pi.instZero.{u1, 0} ι (fun (a._@.Mathlib.Topology.Instances.ENNReal._hyg.26995 : ι) => Real) (fun (i : ι) => Real.instZeroReal)))) f) -> (forall (u : Finset.{u1} ι), LE.le.{0} Real Real.instLEReal (Finset.sum.{0, u1} Real ι Real.instAddCommMonoidReal u (fun (x : ι) => f x)) c) -> (Summable.{0, u1} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)
Case conversion may be inaccurate. Consider using '#align summable_of_sum_le summable_of_sum_leₓ'. -/
theorem summable_of_sum_le {ι : Type _} {f : ι → ℝ} {c : ℝ} (hf : 0 ≤ f)
    (h : ∀ u : Finset ι, (∑ x in u, f x) ≤ c) : Summable f :=
  ⟨⨆ u : Finset ι, ∑ x in u, f x,
    tendsto_atTop_ciSup (Finset.sum_mono_set_of_nonneg hf) ⟨c, fun y ⟨u, hu⟩ => hu ▸ h u⟩⟩
#align summable_of_sum_le summable_of_sum_le

/- warning: summable_of_sum_range_le -> summable_of_sum_range_le is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real} {c : Real}, (forall (n : Nat), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f n)) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => f i)) c) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)
but is expected to have type
  forall {f : Nat -> Real} {c : Real}, (forall (n : Nat), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f n)) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => f i)) c) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)
Case conversion may be inaccurate. Consider using '#align summable_of_sum_range_le summable_of_sum_range_leₓ'. -/
theorem summable_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, (∑ i in Finset.range n, f i) ≤ c) : Summable f :=
  by
  apply (summable_iff_not_tendsto_nat_atTop_of_nonneg hf).2 fun H => _
  rcases exists_lt_of_tendsto_at_top H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))
#align summable_of_sum_range_le summable_of_sum_range_le

/- warning: real.tsum_le_of_sum_range_le -> Real.tsum_le_of_sum_range_le is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real} {c : Real}, (forall (n : Nat), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f n)) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => f i)) c) -> (LE.le.{0} Real Real.hasLe (tsum.{0, 0} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (n : Nat) => f n)) c)
but is expected to have type
  forall {f : Nat -> Real} {c : Real}, (forall (n : Nat), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f n)) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => f i)) c) -> (LE.le.{0} Real Real.instLEReal (tsum.{0, 0} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (n : Nat) => f n)) c)
Case conversion may be inaccurate. Consider using '#align real.tsum_le_of_sum_range_le Real.tsum_le_of_sum_range_leₓ'. -/
theorem Real.tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, (∑ i in Finset.range n, f i) ≤ c) : (∑' n, f n) ≤ c :=
  tsum_le_of_sum_range_le (summable_of_sum_range_le hf h) h
#align real.tsum_le_of_sum_range_le Real.tsum_le_of_sum_range_le

/- warning: tsum_lt_tsum_of_nonneg -> tsum_lt_tsum_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {i : Nat} {f : Nat -> Real} {g : Nat -> Real}, (forall (b : Nat), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f b)) -> (forall (b : Nat), LE.le.{0} Real Real.hasLe (f b) (g b)) -> (LT.lt.{0} Real Real.hasLt (f i) (g i)) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (LT.lt.{0} Real Real.hasLt (tsum.{0, 0} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (n : Nat) => f n)) (tsum.{0, 0} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (n : Nat) => g n)))
but is expected to have type
  forall {i : Nat} {f : Nat -> Real} {g : Nat -> Real}, (forall (b : Nat), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f b)) -> (forall (b : Nat), LE.le.{0} Real Real.instLEReal (f b) (g b)) -> (LT.lt.{0} Real Real.instLTReal (f i) (g i)) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (LT.lt.{0} Real Real.instLTReal (tsum.{0, 0} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (n : Nat) => f n)) (tsum.{0, 0} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (n : Nat) => g n)))
Case conversion may be inaccurate. Consider using '#align tsum_lt_tsum_of_nonneg tsum_lt_tsum_of_nonnegₓ'. -/
/-- If a sequence `f` with non-negative terms is dominated by a sequence `g` with summable
series and at least one term of `f` is strictly smaller than the corresponding term in `g`,
then the series of `f` is strictly smaller than the series of `g`. -/
theorem tsum_lt_tsum_of_nonneg {i : ℕ} {f g : ℕ → ℝ} (h0 : ∀ b : ℕ, 0 ≤ f b)
    (h : ∀ b : ℕ, f b ≤ g b) (hi : f i < g i) (hg : Summable g) : (∑' n, f n) < ∑' n, g n :=
  tsum_lt_tsum h hi (summable_of_nonneg_of_le h0 h hg) hg
#align tsum_lt_tsum_of_nonneg tsum_lt_tsum_of_nonneg

section

variable [EMetricSpace β]

open ENNReal Filter Emetric

/- warning: edist_ne_top_of_mem_ball -> edist_ne_top_of_mem_ball is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : EMetricSpace.{u1} β] {a : β} {r : ENNReal} (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (EMetric.ball.{u1} β (EMetricSpace.toPseudoEmetricSpace.{u1} β _inst_1) a r)) (y : coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (EMetric.ball.{u1} β (EMetricSpace.toPseudoEmetricSpace.{u1} β _inst_1) a r)), Ne.{1} ENNReal (EDist.edist.{u1} β (PseudoEMetricSpace.toHasEdist.{u1} β (EMetricSpace.toPseudoEmetricSpace.{u1} β _inst_1)) (Subtype.val.{succ u1} β (fun (x : β) => Membership.Mem.{u1, u1} β (Set.{u1} β) (Set.hasMem.{u1} β) x (EMetric.ball.{u1} β (EMetricSpace.toPseudoEmetricSpace.{u1} β _inst_1) a r)) x) (Subtype.val.{succ u1} β (fun (x : β) => Membership.Mem.{u1, u1} β (Set.{u1} β) (Set.hasMem.{u1} β) x (EMetric.ball.{u1} β (EMetricSpace.toPseudoEmetricSpace.{u1} β _inst_1) a r)) y)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : EMetricSpace.{u1} β] {a : β} {r : ENNReal} (x : Set.Elem.{u1} β (EMetric.ball.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_1) a r)) (y : Set.Elem.{u1} β (EMetric.ball.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_1) a r)), Ne.{1} ENNReal (EDist.edist.{u1} β (PseudoEMetricSpace.toEDist.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_1)) (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (EMetric.ball.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_1) a r)) x) (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (EMetric.ball.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_1) a r)) y)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align edist_ne_top_of_mem_ball edist_ne_top_of_mem_ballₓ'. -/
/-- In an emetric ball, the distance between points is everywhere finite -/
theorem edist_ne_top_of_mem_ball {a : β} {r : ℝ≥0∞} (x y : ball a r) : edist x.1 y.1 ≠ ⊤ :=
  lt_top_iff_ne_top.1 <|
    calc
      edist x y ≤ edist a x + edist a y := edist_triangle_left x.1 y.1 a
      _ < r + r := by rw [edist_comm a x, edist_comm a y] <;> exact add_lt_add x.2 y.2
      _ ≤ ⊤ := le_top
      
#align edist_ne_top_of_mem_ball edist_ne_top_of_mem_ball

#print metricSpaceEMetricBall /-
/-- Each ball in an extended metric space gives us a metric space, as the edist
is everywhere finite. -/
def metricSpaceEMetricBall (a : β) (r : ℝ≥0∞) : MetricSpace (ball a r) :=
  EMetricSpace.toMetricSpace edist_ne_top_of_mem_ball
#align metric_space_emetric_ball metricSpaceEMetricBall
-/

attribute [local instance] metricSpaceEMetricBall

#print nhds_eq_nhds_emetric_ball /-
theorem nhds_eq_nhds_emetric_ball (a x : β) (r : ℝ≥0∞) (h : x ∈ ball a r) :
    𝓝 x = map (coe : ball a r → β) (𝓝 ⟨x, h⟩) :=
  (map_nhds_subtype_coe_eq_nhds _ <| IsOpen.mem_nhds EMetric.isOpen_ball h).symm
#align nhds_eq_nhds_emetric_ball nhds_eq_nhds_emetric_ball
-/

end

section

variable [PseudoEMetricSpace α]

open Emetric

/- warning: tendsto_iff_edist_tendsto_0 -> tendsto_iff_edist_tendsto_0 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {l : Filter.{u2} β} {f : β -> α} {y : α}, Iff (Filter.Tendsto.{u2, u1} β α f l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) y)) (Filter.Tendsto.{u2, 0} β ENNReal (fun (x : β) => EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f x) y) l (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {l : Filter.{u2} β} {f : β -> α} {y : α}, Iff (Filter.Tendsto.{u2, u1} β α f l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) y)) (Filter.Tendsto.{u2, 0} β ENNReal (fun (x : β) => EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f x) y) l (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align tendsto_iff_edist_tendsto_0 tendsto_iff_edist_tendsto_0ₓ'. -/
theorem tendsto_iff_edist_tendsto_0 {l : Filter β} {f : β → α} {y : α} :
    Tendsto f l (𝓝 y) ↔ Tendsto (fun x => edist (f x) y) l (𝓝 0) := by
  simp only [emetric.nhds_basis_eball.tendsto_right_iff, EMetric.mem_ball,
    @tendsto_order ℝ≥0∞ β _ _, forall_prop_of_false ENNReal.not_lt_zero, forall_const, true_and_iff]
#align tendsto_iff_edist_tendsto_0 tendsto_iff_edist_tendsto_0

/- warning: emetric.cauchy_seq_iff_le_tendsto_0 -> EMetric.cauchySeq_iff_le_tendsto_0 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {s : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 s) (Exists.{succ u2} (β -> ENNReal) (fun (b : β -> ENNReal) => And (forall (n : β) (m : β) (N : β), (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N n) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N m) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (s n) (s m)) (b N))) (Filter.Tendsto.{u2, 0} β ENNReal b (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {s : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 s) (Exists.{succ u2} (β -> ENNReal) (fun (b : β -> ENNReal) => And (forall (n : β) (m : β) (N : β), (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N n) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N m) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (s n) (s m)) (b N))) (Filter.Tendsto.{u2, 0} β ENNReal b (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))))
Case conversion may be inaccurate. Consider using '#align emetric.cauchy_seq_iff_le_tendsto_0 EMetric.cauchySeq_iff_le_tendsto_0ₓ'. -/
/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
theorem EMetric.cauchySeq_iff_le_tendsto_0 [Nonempty β] [SemilatticeSup β] {s : β → α} :
    CauchySeq s ↔
      ∃ b : β → ℝ≥0∞,
        (∀ n m N : β, N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N) ∧ Tendsto b atTop (𝓝 0) :=
  ⟨by
    intro hs
    rw [EMetric.cauchySeq_iff] at hs
    /- `s` is Cauchy sequence. The sequence `b` will be constructed by taking
      the supremum of the distances between `s n` and `s m` for `n m ≥ N`-/
    let b N := Sup ((fun p : β × β => edist (s p.1) (s p.2)) '' { p | p.1 ≥ N ∧ p.2 ≥ N })
    --Prove that it bounds the distances of points in the Cauchy sequence
    have C : ∀ n m N, N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N :=
      by
      refine' fun m n N hm hn => le_sSup _
      use Prod.mk m n
      simp only [and_true_iff, eq_self_iff_true, Set.mem_setOf_eq]
      exact ⟨hm, hn⟩
    --Prove that it tends to `0`, by using the Cauchy property of `s`
    have D : tendsto b at_top (𝓝 0) :=
      by
      refine' tendsto_order.2 ⟨fun a ha => absurd ha ENNReal.not_lt_zero, fun ε εpos => _⟩
      rcases exists_between εpos with ⟨δ, δpos, δlt⟩
      rcases hs δ δpos with ⟨N, hN⟩
      refine' Filter.mem_atTop_sets.2 ⟨N, fun n hn => _⟩
      have : b n ≤ δ :=
        sSup_le
          (by
            simp only [and_imp, Set.mem_image, Set.mem_setOf_eq, exists_imp, Prod.exists]
            intro d p q hp hq hd
            rw [← hd]
            exact le_of_lt (hN p (le_trans hn hp) q (le_trans hn hq)))
      simpa using lt_of_le_of_lt this δlt
    -- Conclude
    exact ⟨b, ⟨C, D⟩⟩,
    by
    rintro ⟨b, ⟨b_bound, b_lim⟩⟩
    /-b : ℕ → ℝ, b_bound : ∀ (n m N : ℕ), N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N,
        b_lim : tendsto b at_top (𝓝 0)-/
    refine' EMetric.cauchySeq_iff.2 fun ε εpos => _
    have : ∀ᶠ n in at_top, b n < ε := (tendsto_order.1 b_lim).2 _ εpos
    rcases Filter.mem_atTop_sets.1 this with ⟨N, hN⟩
    exact
      ⟨N, fun m hm n hn =>
        calc
          edist (s m) (s n) ≤ b N := b_bound m n N hm hn
          _ < ε := hN _ (le_refl N)
          ⟩⟩
#align emetric.cauchy_seq_iff_le_tendsto_0 EMetric.cauchySeq_iff_le_tendsto_0

/- warning: continuous_of_le_add_edist -> continuous_of_le_add_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : α -> ENNReal} (C : ENNReal), (Ne.{1} ENNReal C (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall (x : α) (y : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f y) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) C (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y)))) -> (Continuous.{u1, 0} α ENNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) ENNReal.topologicalSpace f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : α -> ENNReal} (C : ENNReal), (Ne.{1} ENNReal C (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall (x : α) (y : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f y) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) C (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y)))) -> (Continuous.{u1, 0} α ENNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) ENNReal.instTopologicalSpaceENNReal f)
Case conversion may be inaccurate. Consider using '#align continuous_of_le_add_edist continuous_of_le_add_edistₓ'. -/
theorem continuous_of_le_add_edist {f : α → ℝ≥0∞} (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (h : ∀ x y, f x ≤ f y + C * edist x y) : Continuous f :=
  by
  rcases eq_or_ne C 0 with (rfl | C0)
  · simp only [MulZeroClass.zero_mul, add_zero] at h
    exact continuous_of_const fun x y => le_antisymm (h _ _) (h _ _)
  · refine' continuous_iff_continuousAt.2 fun x => _
    by_cases hx : f x = ∞
    · have : f =ᶠ[𝓝 x] fun _ => ∞ :=
        by
        filter_upwards [EMetric.ball_mem_nhds x ENNReal.coe_lt_top]
        refine' fun y (hy : edist y x < ⊤) => _
        rw [edist_comm] at hy
        simpa [hx, ENNReal.mul_ne_top hC hy.ne] using h x y
      exact this.continuous_at
    · refine' (ENNReal.tendsto_nhds hx).2 fun ε (ε0 : 0 < ε) => _
      filter_upwards [EMetric.closedBall_mem_nhds x (ENNReal.div_pos_iff.2 ⟨ε0.ne', hC⟩)]
      have hεC : C * (ε / C) = ε := ENNReal.mul_div_cancel' C0 hC
      refine' fun y (hy : edist y x ≤ ε / C) => ⟨tsub_le_iff_right.2 _, _⟩
      · rw [edist_comm] at hy
        calc
          f x ≤ f y + C * edist x y := h x y
          _ ≤ f y + C * (ε / C) := (add_le_add_left (mul_le_mul_left' hy C) (f y))
          _ = f y + ε := by rw [hεC]
          
      ·
        calc
          f y ≤ f x + C * edist y x := h y x
          _ ≤ f x + C * (ε / C) := (add_le_add_left (mul_le_mul_left' hy C) (f x))
          _ = f x + ε := by rw [hεC]
          
#align continuous_of_le_add_edist continuous_of_le_add_edist

/- warning: continuous_edist -> continuous_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Continuous.{u1, 0} (Prod.{u1, u1} α α) ENNReal (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1))) ENNReal.topologicalSpace (fun (p : Prod.{u1, u1} α α) => EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Continuous.{u1, 0} (Prod.{u1, u1} α α) ENNReal (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1))) ENNReal.instTopologicalSpaceENNReal (fun (p : Prod.{u1, u1} α α) => EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
Case conversion may be inaccurate. Consider using '#align continuous_edist continuous_edistₓ'. -/
theorem continuous_edist : Continuous fun p : α × α => edist p.1 p.2 :=
  by
  apply continuous_of_le_add_edist 2 (by norm_num)
  rintro ⟨x, y⟩ ⟨x', y'⟩
  calc
    edist x y ≤ edist x x' + edist x' y' + edist y' y := edist_triangle4 _ _ _ _
    _ = edist x' y' + (edist x x' + edist y y') := by simp [edist_comm] <;> cc
    _ ≤ edist x' y' + (edist (x, y) (x', y') + edist (x, y) (x', y')) :=
      (add_le_add_left (add_le_add (le_max_left _ _) (le_max_right _ _)) _)
    _ = edist x' y' + 2 * edist (x, y) (x', y') := by rw [← mul_two, mul_comm]
    
#align continuous_edist continuous_edist

/- warning: continuous.edist -> Continuous.edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {g : β -> α}, (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) f) -> (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) g) -> (Continuous.{u2, 0} β ENNReal _inst_2 ENNReal.topologicalSpace (fun (b : β) => EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f b) (g b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {g : β -> α}, (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) f) -> (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) g) -> (Continuous.{u2, 0} β ENNReal _inst_2 ENNReal.instTopologicalSpaceENNReal (fun (b : β) => EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f b) (g b)))
Case conversion may be inaccurate. Consider using '#align continuous.edist Continuous.edistₓ'. -/
@[continuity]
theorem Continuous.edist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => edist (f b) (g b) :=
  continuous_edist.comp (hf.prod_mk hg : _)
#align continuous.edist Continuous.edist

/- warning: filter.tendsto.edist -> Filter.Tendsto.edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : β -> α} {g : β -> α} {x : Filter.{u2} β} {a : α} {b : α}, (Filter.Tendsto.{u2, u1} β α f x (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (Filter.Tendsto.{u2, u1} β α g x (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) b)) -> (Filter.Tendsto.{u2, 0} β ENNReal (fun (x : β) => EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f x) (g x)) x (nhds.{0} ENNReal ENNReal.topologicalSpace (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) a b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : β -> α} {g : β -> α} {x : Filter.{u2} β} {a : α} {b : α}, (Filter.Tendsto.{u2, u1} β α f x (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (Filter.Tendsto.{u2, u1} β α g x (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) b)) -> (Filter.Tendsto.{u2, 0} β ENNReal (fun (x : β) => EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f x) (g x)) x (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) a b)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.edist Filter.Tendsto.edistₓ'. -/
theorem Filter.Tendsto.edist {f g : β → α} {x : Filter β} {a b : α} (hf : Tendsto f x (𝓝 a))
    (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => edist (f x) (g x)) x (𝓝 (edist a b)) :=
  (continuous_edist.Tendsto (a, b)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.edist Filter.Tendsto.edist

/- warning: cauchy_seq_of_edist_le_of_tsum_ne_top -> cauchySeq_of_edist_le_of_tsum_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> ENNReal), (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (Ne.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat d) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (CauchySeq.{u1, 0} α Nat (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> ENNReal), (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (Ne.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat d) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (CauchySeq.{u1, 0} α Nat (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) f)
Case conversion may be inaccurate. Consider using '#align cauchy_seq_of_edist_le_of_tsum_ne_top cauchySeq_of_edist_le_of_tsum_ne_topₓ'. -/
theorem cauchySeq_of_edist_le_of_tsum_ne_top {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : tsum d ≠ ∞) : CauchySeq f :=
  by
  lift d to ℕ → NNReal using fun i => ENNReal.ne_top_of_tsum_ne_top hd i
  rw [ENNReal.tsum_coe_ne_top_iff_summable] at hd
  exact cauchySeq_of_edist_le_of_summable d hf hd
#align cauchy_seq_of_edist_le_of_tsum_ne_top cauchySeq_of_edist_le_of_tsum_ne_top

#print EMetric.isClosed_ball /-
theorem EMetric.isClosed_ball {a : α} {r : ℝ≥0∞} : IsClosed (closedBall a r) :=
  isClosed_le (continuous_id.edist continuous_const) continuous_const
#align emetric.is_closed_ball EMetric.isClosed_ball
-/

#print EMetric.diam_closure /-
@[simp]
theorem EMetric.diam_closure (s : Set α) : diam (closure s) = diam s :=
  by
  refine' le_antisymm (diam_le fun x hx y hy => _) (diam_mono subset_closure)
  have : edist x y ∈ closure (Iic (diam s)) :=
    map_mem_closure₂ continuous_edist hx hy fun x hx y hy => edist_le_diam_of_mem hx hy
  rwa [closure_Iic] at this
#align emetric.diam_closure EMetric.diam_closure
-/

#print Metric.diam_closure /-
@[simp]
theorem Metric.diam_closure {α : Type _} [PseudoMetricSpace α] (s : Set α) :
    Metric.diam (closure s) = diam s := by simp only [Metric.diam, EMetric.diam_closure]
#align metric.diam_closure Metric.diam_closure
-/

/- warning: is_closed_set_of_lipschitz_on_with -> isClosed_setOf_lipschitzOnWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : PseudoEMetricSpace.{u1} α] [_inst_3 : PseudoEMetricSpace.{u2} β] (K : NNReal) (s : Set.{u1} α), IsClosed.{max u1 u2} (α -> β) (Pi.topologicalSpace.{u1, u2} α (fun (ᾰ : α) => β) (fun (a : α) => UniformSpace.toTopologicalSpace.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_3))) (setOf.{max u1 u2} (α -> β) (fun (f : α -> β) => LipschitzOnWith.{u1, u2} α β _inst_2 _inst_3 K f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : PseudoEMetricSpace.{u2} α] [_inst_3 : PseudoEMetricSpace.{u1} β] (K : NNReal) (s : Set.{u2} α), IsClosed.{max u2 u1} (α -> β) (Pi.topologicalSpace.{u2, u1} α (fun (ᾰ : α) => β) (fun (a : α) => UniformSpace.toTopologicalSpace.{u1} β (PseudoEMetricSpace.toUniformSpace.{u1} β _inst_3))) (setOf.{max u2 u1} (α -> β) (fun (f : α -> β) => LipschitzOnWith.{u2, u1} α β _inst_2 _inst_3 K f s))
Case conversion may be inaccurate. Consider using '#align is_closed_set_of_lipschitz_on_with isClosed_setOf_lipschitzOnWithₓ'. -/
theorem isClosed_setOf_lipschitzOnWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0)
    (s : Set α) : IsClosed { f : α → β | LipschitzOnWith K f s } :=
  by
  simp only [LipschitzOnWith, set_of_forall]
  refine' isClosed_biInter fun x hx => isClosed_biInter fun y hy => isClosed_le _ _
  exacts[Continuous.edist (continuous_apply x) (continuous_apply y), continuous_const]
#align is_closed_set_of_lipschitz_on_with isClosed_setOf_lipschitzOnWith

/- warning: is_closed_set_of_lipschitz_with -> isClosed_setOf_lipschitzWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : PseudoEMetricSpace.{u1} α] [_inst_3 : PseudoEMetricSpace.{u2} β] (K : NNReal), IsClosed.{max u1 u2} (α -> β) (Pi.topologicalSpace.{u1, u2} α (fun (ᾰ : α) => β) (fun (a : α) => UniformSpace.toTopologicalSpace.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_3))) (setOf.{max u1 u2} (α -> β) (fun (f : α -> β) => LipschitzWith.{u1, u2} α β _inst_2 _inst_3 K f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : PseudoEMetricSpace.{u2} α] [_inst_3 : PseudoEMetricSpace.{u1} β] (K : NNReal), IsClosed.{max u2 u1} (α -> β) (Pi.topologicalSpace.{u2, u1} α (fun (ᾰ : α) => β) (fun (a : α) => UniformSpace.toTopologicalSpace.{u1} β (PseudoEMetricSpace.toUniformSpace.{u1} β _inst_3))) (setOf.{max u2 u1} (α -> β) (fun (f : α -> β) => LipschitzWith.{u2, u1} α β _inst_2 _inst_3 K f))
Case conversion may be inaccurate. Consider using '#align is_closed_set_of_lipschitz_with isClosed_setOf_lipschitzWithₓ'. -/
theorem isClosed_setOf_lipschitzWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) :
    IsClosed { f : α → β | LipschitzWith K f } := by
  simp only [← lipschitz_on_univ, isClosed_setOf_lipschitzOnWith]
#align is_closed_set_of_lipschitz_with isClosed_setOf_lipschitzWith

namespace Real

/- warning: real.ediam_eq -> Real.ediam_eq is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real}, (Metric.Bounded.{0} Real Real.pseudoMetricSpace s) -> (Eq.{1} ENNReal (EMetric.diam.{0} Real (PseudoMetricSpace.toPseudoEMetricSpace.{0} Real Real.pseudoMetricSpace) s) (ENNReal.ofReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (SupSet.sSup.{0} Real Real.hasSup s) (InfSet.sInf.{0} Real Real.hasInf s))))
but is expected to have type
  forall {s : Set.{0} Real}, (Metric.Bounded.{0} Real Real.pseudoMetricSpace s) -> (Eq.{1} ENNReal (EMetric.diam.{0} Real (EMetricSpace.toPseudoEMetricSpace.{0} Real (MetricSpace.toEMetricSpace.{0} Real Real.metricSpace)) s) (ENNReal.ofReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (SupSet.sSup.{0} Real Real.instSupSetReal s) (InfSet.sInf.{0} Real Real.instInfSetReal s))))
Case conversion may be inaccurate. Consider using '#align real.ediam_eq Real.ediam_eqₓ'. -/
/-- For a bounded set `s : set ℝ`, its `emetric.diam` is equal to `Sup s - Inf s` reinterpreted as
`ℝ≥0∞`. -/
theorem ediam_eq {s : Set ℝ} (h : Bounded s) : EMetric.diam s = ENNReal.ofReal (sSup s - sInf s) :=
  by
  rcases eq_empty_or_nonempty s with (rfl | hne); · simp
  refine' le_antisymm (Metric.ediam_le_of_forall_dist_le fun x hx y hy => _) _
  · have := Real.subset_Icc_sInf_sSup_of_bounded h
    exact Real.dist_le_of_mem_Icc (this hx) (this hy)
  · apply ENNReal.ofReal_le_of_le_toReal
    rw [← Metric.diam, ← Metric.diam_closure]
    have h' := Real.bounded_iff_bddBelow_bddAbove.1 h
    calc
      Sup s - Inf s ≤ dist (Sup s) (Inf s) := le_abs_self _
      _ ≤ diam (closure s) :=
        dist_le_diam_of_mem h.closure (csSup_mem_closure hne h'.2) (csInf_mem_closure hne h'.1)
      
#align real.ediam_eq Real.ediam_eq

/- warning: real.diam_eq -> Real.diam_eq is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real}, (Metric.Bounded.{0} Real Real.pseudoMetricSpace s) -> (Eq.{1} Real (Metric.diam.{0} Real Real.pseudoMetricSpace s) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (SupSet.sSup.{0} Real Real.hasSup s) (InfSet.sInf.{0} Real Real.hasInf s)))
but is expected to have type
  forall {s : Set.{0} Real}, (Metric.Bounded.{0} Real Real.pseudoMetricSpace s) -> (Eq.{1} Real (Metric.diam.{0} Real Real.pseudoMetricSpace s) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (SupSet.sSup.{0} Real Real.instSupSetReal s) (InfSet.sInf.{0} Real Real.instInfSetReal s)))
Case conversion may be inaccurate. Consider using '#align real.diam_eq Real.diam_eqₓ'. -/
/-- For a bounded set `s : set ℝ`, its `metric.diam` is equal to `Sup s - Inf s`. -/
theorem diam_eq {s : Set ℝ} (h : Bounded s) : Metric.diam s = sSup s - sInf s :=
  by
  rw [Metric.diam, Real.ediam_eq h, ENNReal.toReal_ofReal]
  rw [Real.bounded_iff_bddBelow_bddAbove] at h
  exact sub_nonneg.2 (Real.sInf_le_sSup s h.1 h.2)
#align real.diam_eq Real.diam_eq

/- warning: real.ediam_Ioo -> Real.ediam_Ioo is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), Eq.{1} ENNReal (EMetric.diam.{0} Real (PseudoMetricSpace.toPseudoEMetricSpace.{0} Real Real.pseudoMetricSpace) (Set.Ioo.{0} Real Real.preorder a b)) (ENNReal.ofReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) b a))
but is expected to have type
  forall (a : Real) (b : Real), Eq.{1} ENNReal (EMetric.diam.{0} Real (EMetricSpace.toPseudoEMetricSpace.{0} Real (MetricSpace.toEMetricSpace.{0} Real Real.metricSpace)) (Set.Ioo.{0} Real Real.instPreorderReal a b)) (ENNReal.ofReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) b a))
Case conversion may be inaccurate. Consider using '#align real.ediam_Ioo Real.ediam_Iooₓ'. -/
@[simp]
theorem ediam_Ioo (a b : ℝ) : EMetric.diam (Ioo a b) = ENNReal.ofReal (b - a) :=
  by
  rcases le_or_lt b a with (h | h)
  · simp [h]
  · rw [Real.ediam_eq (bounded_Ioo _ _), csSup_Ioo h, csInf_Ioo h]
#align real.ediam_Ioo Real.ediam_Ioo

/- warning: real.ediam_Icc -> Real.ediam_Icc is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), Eq.{1} ENNReal (EMetric.diam.{0} Real (PseudoMetricSpace.toPseudoEMetricSpace.{0} Real Real.pseudoMetricSpace) (Set.Icc.{0} Real Real.preorder a b)) (ENNReal.ofReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) b a))
but is expected to have type
  forall (a : Real) (b : Real), Eq.{1} ENNReal (EMetric.diam.{0} Real (EMetricSpace.toPseudoEMetricSpace.{0} Real (MetricSpace.toEMetricSpace.{0} Real Real.metricSpace)) (Set.Icc.{0} Real Real.instPreorderReal a b)) (ENNReal.ofReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) b a))
Case conversion may be inaccurate. Consider using '#align real.ediam_Icc Real.ediam_Iccₓ'. -/
@[simp]
theorem ediam_Icc (a b : ℝ) : EMetric.diam (Icc a b) = ENNReal.ofReal (b - a) :=
  by
  rcases le_or_lt a b with (h | h)
  · rw [Real.ediam_eq (bounded_Icc _ _), csSup_Icc h, csInf_Icc h]
  · simp [h, h.le]
#align real.ediam_Icc Real.ediam_Icc

/- warning: real.ediam_Ico -> Real.ediam_Ico is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), Eq.{1} ENNReal (EMetric.diam.{0} Real (PseudoMetricSpace.toPseudoEMetricSpace.{0} Real Real.pseudoMetricSpace) (Set.Ico.{0} Real Real.preorder a b)) (ENNReal.ofReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) b a))
but is expected to have type
  forall (a : Real) (b : Real), Eq.{1} ENNReal (EMetric.diam.{0} Real (EMetricSpace.toPseudoEMetricSpace.{0} Real (MetricSpace.toEMetricSpace.{0} Real Real.metricSpace)) (Set.Ico.{0} Real Real.instPreorderReal a b)) (ENNReal.ofReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) b a))
Case conversion may be inaccurate. Consider using '#align real.ediam_Ico Real.ediam_Icoₓ'. -/
@[simp]
theorem ediam_Ico (a b : ℝ) : EMetric.diam (Ico a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ diam_mono Ico_subset_Icc_self)
    (ediam_Ioo a b ▸ diam_mono Ioo_subset_Ico_self)
#align real.ediam_Ico Real.ediam_Ico

/- warning: real.ediam_Ioc -> Real.ediam_Ioc is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), Eq.{1} ENNReal (EMetric.diam.{0} Real (PseudoMetricSpace.toPseudoEMetricSpace.{0} Real Real.pseudoMetricSpace) (Set.Ioc.{0} Real Real.preorder a b)) (ENNReal.ofReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) b a))
but is expected to have type
  forall (a : Real) (b : Real), Eq.{1} ENNReal (EMetric.diam.{0} Real (EMetricSpace.toPseudoEMetricSpace.{0} Real (MetricSpace.toEMetricSpace.{0} Real Real.metricSpace)) (Set.Ioc.{0} Real Real.instPreorderReal a b)) (ENNReal.ofReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) b a))
Case conversion may be inaccurate. Consider using '#align real.ediam_Ioc Real.ediam_Iocₓ'. -/
@[simp]
theorem ediam_Ioc (a b : ℝ) : EMetric.diam (Ioc a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ diam_mono Ioc_subset_Icc_self)
    (ediam_Ioo a b ▸ diam_mono Ioo_subset_Ioc_self)
#align real.ediam_Ioc Real.ediam_Ioc

/- warning: real.diam_Icc -> Real.diam_Icc is a dubious translation:
lean 3 declaration is
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.hasLe a b) -> (Eq.{1} Real (Metric.diam.{0} Real Real.pseudoMetricSpace (Set.Icc.{0} Real Real.preorder a b)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) b a))
but is expected to have type
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.instLEReal a b) -> (Eq.{1} Real (Metric.diam.{0} Real Real.pseudoMetricSpace (Set.Icc.{0} Real Real.instPreorderReal a b)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) b a))
Case conversion may be inaccurate. Consider using '#align real.diam_Icc Real.diam_Iccₓ'. -/
theorem diam_Icc {a b : ℝ} (h : a ≤ b) : Metric.diam (Icc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal, sub_nonneg.2 h]
#align real.diam_Icc Real.diam_Icc

/- warning: real.diam_Ico -> Real.diam_Ico is a dubious translation:
lean 3 declaration is
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.hasLe a b) -> (Eq.{1} Real (Metric.diam.{0} Real Real.pseudoMetricSpace (Set.Ico.{0} Real Real.preorder a b)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) b a))
but is expected to have type
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.instLEReal a b) -> (Eq.{1} Real (Metric.diam.{0} Real Real.pseudoMetricSpace (Set.Ico.{0} Real Real.instPreorderReal a b)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) b a))
Case conversion may be inaccurate. Consider using '#align real.diam_Ico Real.diam_Icoₓ'. -/
theorem diam_Ico {a b : ℝ} (h : a ≤ b) : Metric.diam (Ico a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal, sub_nonneg.2 h]
#align real.diam_Ico Real.diam_Ico

/- warning: real.diam_Ioc -> Real.diam_Ioc is a dubious translation:
lean 3 declaration is
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.hasLe a b) -> (Eq.{1} Real (Metric.diam.{0} Real Real.pseudoMetricSpace (Set.Ioc.{0} Real Real.preorder a b)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) b a))
but is expected to have type
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.instLEReal a b) -> (Eq.{1} Real (Metric.diam.{0} Real Real.pseudoMetricSpace (Set.Ioc.{0} Real Real.instPreorderReal a b)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) b a))
Case conversion may be inaccurate. Consider using '#align real.diam_Ioc Real.diam_Iocₓ'. -/
theorem diam_Ioc {a b : ℝ} (h : a ≤ b) : Metric.diam (Ioc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal, sub_nonneg.2 h]
#align real.diam_Ioc Real.diam_Ioc

/- warning: real.diam_Ioo -> Real.diam_Ioo is a dubious translation:
lean 3 declaration is
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.hasLe a b) -> (Eq.{1} Real (Metric.diam.{0} Real Real.pseudoMetricSpace (Set.Ioo.{0} Real Real.preorder a b)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) b a))
but is expected to have type
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.instLEReal a b) -> (Eq.{1} Real (Metric.diam.{0} Real Real.pseudoMetricSpace (Set.Ioo.{0} Real Real.instPreorderReal a b)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) b a))
Case conversion may be inaccurate. Consider using '#align real.diam_Ioo Real.diam_Iooₓ'. -/
theorem diam_Ioo {a b : ℝ} (h : a ≤ b) : Metric.diam (Ioo a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal, sub_nonneg.2 h]
#align real.diam_Ioo Real.diam_Ioo

end Real

/- warning: edist_le_tsum_of_edist_le_of_tendsto -> edist_le_tsum_of_edist_le_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> ENNReal), (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (forall {a : α}, (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f n) a) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (m : Nat) => d (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n m)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> ENNReal), (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (forall {a : α}, (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f n) a) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (m : Nat) => d (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n m)))))
Case conversion may be inaccurate. Consider using '#align edist_le_tsum_of_edist_le_of_tendsto edist_le_tsum_of_edist_le_of_tendstoₓ'. -/
/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f n` to the limit is bounded by `∑'_{k=n}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    edist (f n) a ≤ ∑' m, d (n + m) :=
  by
  refine' le_of_tendsto (tendsto_const_nhds.edist ha) (mem_at_top_sets.2 ⟨n, fun m hnm => _⟩)
  refine' le_trans (edist_le_Ico_sum_of_edist_le hnm fun k _ _ => hf k) _
  rw [Finset.sum_Ico_eq_sum_range]
  exact sum_le_tsum _ (fun _ _ => zero_le _) ENNReal.summable
#align edist_le_tsum_of_edist_le_of_tendsto edist_le_tsum_of_edist_le_of_tendsto

/- warning: edist_le_tsum_of_edist_le_of_tendsto₀ -> edist_le_tsum_of_edist_le_of_tendsto₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> ENNReal), (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (forall {a : α}, (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) a) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (m : Nat) => d m))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> ENNReal), (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (forall {a : α}, (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) a) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (m : Nat) => d m))))
Case conversion may be inaccurate. Consider using '#align edist_le_tsum_of_edist_le_of_tendsto₀ edist_le_tsum_of_edist_le_of_tendsto₀ₓ'. -/
/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f 0` to the limit is bounded by `∑'_{k=0}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto₀ {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    edist (f 0) a ≤ ∑' m, d m := by simpa using edist_le_tsum_of_edist_le_of_tendsto d hf ha 0
#align edist_le_tsum_of_edist_le_of_tendsto₀ edist_le_tsum_of_edist_le_of_tendsto₀

end

--section
