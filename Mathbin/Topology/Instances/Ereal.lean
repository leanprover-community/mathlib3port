/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.instances.ereal
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rat.Encodable
import Mathbin.Data.Real.Ereal
import Mathbin.Topology.Algebra.Order.MonotoneContinuity
import Mathbin.Topology.Instances.Ennreal

/-!
# Topological structure on `ereal`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We endow `ereal` with the order topology, and prove basic properties of this topology.

## Main results

* `coe : ℝ → ereal` is an open embedding
* `coe : ℝ≥0∞ → ereal` is an embedding
* The addition on `ereal` is continuous except at `(⊥, ⊤)` and at `(⊤, ⊥)`.
* Negation is a homeomorphism on `ereal`.

## Implementation

Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/


noncomputable section

open Classical Set Filter Metric TopologicalSpace

open Classical Topology ENNReal NNReal BigOperators Filter

variable {α : Type _} [TopologicalSpace α]

namespace EReal

instance : TopologicalSpace EReal :=
  Preorder.topology EReal

instance : OrderTopology EReal :=
  ⟨rfl⟩

instance : T2Space EReal := by infer_instance

instance : SecondCountableTopology EReal :=
  ⟨by
    refine'
      ⟨⋃ q : ℚ, {{ a : EReal | a < (q : ℝ) }, { a : EReal | ((q : ℝ) : EReal) < a }},
        countable_Union fun a => (countable_singleton _).insert _, _⟩
    refine'
      le_antisymm
        (le_generateFrom <| by
          simp (config := { contextual := true }) [or_imp, isOpen_lt', isOpen_gt'])
        _
    apply le_generateFrom fun s h => _
    rcases h with ⟨a, hs | hs⟩ <;>
        [rw [show s = ⋃ q ∈ { q : ℚ | a < (q : ℝ) }, { b | ((q : ℝ) : EReal) < b }
            by
            ext x
            simpa only [hs, exists_prop, mem_Union] using
              lt_iff_exists_rat_btwn];rw [show
            s = ⋃ q ∈ { q : ℚ | ((q : ℝ) : EReal) < a }, { b | b < ((q : ℝ) : EReal) }
            by
            ext x
            simpa only [hs, and_comm', exists_prop, mem_Union] using lt_iff_exists_rat_btwn]] <;>
      · apply isOpen_iUnion
        intro q
        apply isOpen_iUnion
        intro hq
        apply generate_open.basic
        exact mem_Union.2 ⟨q, by simp⟩⟩

/-! ### Real coercion -/


/- warning: ereal.embedding_coe -> EReal.embedding_coe is a dubious translation:
lean 3 declaration is
  Embedding.{0, 0} Real EReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) EReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))))
but is expected to have type
  Embedding.{0, 0} Real EReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) EReal.instTopologicalSpaceEReal Real.toEReal
Case conversion may be inaccurate. Consider using '#align ereal.embedding_coe EReal.embedding_coeₓ'. -/
theorem embedding_coe : Embedding (coe : ℝ → EReal) :=
  ⟨⟨by
      refine' le_antisymm _ _
      · rw [@OrderTopology.topology_eq_generate_intervals EReal _, ← coinduced_le_iff_le_induced]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        show IsOpen { b : ℝ | a < ↑b }
        · induction a using EReal.rec
          · simp only [isOpen_univ, bot_lt_coe, set_of_true]
          · simp only [EReal.coe_lt_coe_iff]
            exact isOpen_Ioi
          · simp only [set_of_false, isOpen_empty, not_top_lt]
        show IsOpen { b : ℝ | ↑b < a }
        · induction a using EReal.rec
          · simp only [not_lt_bot, set_of_false, isOpen_empty]
          · simp only [EReal.coe_lt_coe_iff]
            exact isOpen_Iio
          · simp only [isOpen_univ, coe_lt_top, set_of_true]
      · rw [@OrderTopology.topology_eq_generate_intervals ℝ _]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        exact ⟨Ioi a, isOpen_Ioi, by simp [Ioi]⟩
        exact ⟨Iio a, isOpen_Iio, by simp [Iio]⟩⟩, fun a b => by
    simp only [imp_self, EReal.coe_eq_coe_iff]⟩
#align ereal.embedding_coe EReal.embedding_coe

/- warning: ereal.open_embedding_coe -> EReal.openEmbedding_coe is a dubious translation:
lean 3 declaration is
  OpenEmbedding.{0, 0} Real EReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) EReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))))
but is expected to have type
  OpenEmbedding.{0, 0} Real EReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) EReal.instTopologicalSpaceEReal Real.toEReal
Case conversion may be inaccurate. Consider using '#align ereal.open_embedding_coe EReal.openEmbedding_coeₓ'. -/
theorem openEmbedding_coe : OpenEmbedding (coe : ℝ → EReal) :=
  ⟨embedding_coe, by
    convert@isOpen_Ioo EReal _ _ _ ⊥ ⊤
    ext x
    induction x using EReal.rec
    · simp only [left_mem_Ioo, mem_range, coe_ne_bot, exists_false, not_false_iff]
    · simp only [mem_range_self, mem_Ioo, bot_lt_coe, coe_lt_top, and_self_iff]
    · simp only [mem_range, right_mem_Ioo, exists_false, coe_ne_top]⟩
#align ereal.open_embedding_coe EReal.openEmbedding_coe

/- warning: ereal.tendsto_coe -> EReal.tendsto_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> Real} {a : Real}, Iff (Filter.Tendsto.{u1, 0} α EReal (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (m a)) f (nhds.{0} EReal EReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) a))) (Filter.Tendsto.{u1, 0} α Real m f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) a))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> Real} {a : Real}, Iff (Filter.Tendsto.{u1, 0} α EReal (fun (a : α) => Real.toEReal (m a)) f (nhds.{0} EReal EReal.instTopologicalSpaceEReal (Real.toEReal a))) (Filter.Tendsto.{u1, 0} α Real m f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) a))
Case conversion may be inaccurate. Consider using '#align ereal.tendsto_coe EReal.tendsto_coeₓ'. -/
@[norm_cast]
theorem tendsto_coe {α : Type _} {f : Filter α} {m : α → ℝ} {a : ℝ} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe.tendsto_nhds_iff.symm
#align ereal.tendsto_coe EReal.tendsto_coe

/- warning: continuous_coe_real_ereal -> continuous_coe_real_ereal is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} Real EReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) EReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))))
but is expected to have type
  Continuous.{0, 0} Real EReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) EReal.instTopologicalSpaceEReal Real.toEReal
Case conversion may be inaccurate. Consider using '#align continuous_coe_real_ereal continuous_coe_real_erealₓ'. -/
theorem continuous_coe_real_ereal : Continuous (coe : ℝ → EReal) :=
  embedding_coe.Continuous
#align continuous_coe_real_ereal continuous_coe_real_ereal

/- warning: ereal.continuous_coe_iff -> EReal.continuous_coe_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real}, Iff (Continuous.{u1, 0} α EReal _inst_1 EReal.topologicalSpace (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (f a))) (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real}, Iff (Continuous.{u1, 0} α EReal _inst_1 EReal.instTopologicalSpaceEReal (fun (a : α) => Real.toEReal (f a))) (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)
Case conversion may be inaccurate. Consider using '#align ereal.continuous_coe_iff EReal.continuous_coe_iffₓ'. -/
theorem continuous_coe_iff {f : α → ℝ} : (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  embedding_coe.continuous_iff.symm
#align ereal.continuous_coe_iff EReal.continuous_coe_iff

/- warning: ereal.nhds_coe -> EReal.nhds_coe is a dubious translation:
lean 3 declaration is
  forall {r : Real}, Eq.{1} (Filter.{0} EReal) (nhds.{0} EReal EReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) r)) (Filter.map.{0, 0} Real EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) r))
but is expected to have type
  forall {r : Real}, Eq.{1} (Filter.{0} EReal) (nhds.{0} EReal EReal.instTopologicalSpaceEReal (Real.toEReal r)) (Filter.map.{0, 0} Real EReal Real.toEReal (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) r))
Case conversion may be inaccurate. Consider using '#align ereal.nhds_coe EReal.nhds_coeₓ'. -/
theorem nhds_coe {r : ℝ} : 𝓝 (r : EReal) = (𝓝 r).map coe :=
  (openEmbedding_coe.map_nhds_eq r).symm
#align ereal.nhds_coe EReal.nhds_coe

/- warning: ereal.nhds_coe_coe -> EReal.nhds_coe_coe is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : Real}, Eq.{1} (Filter.{0} (Prod.{0, 0} EReal EReal)) (nhds.{0} (Prod.{0, 0} EReal EReal) (Prod.topologicalSpace.{0, 0} EReal EReal EReal.topologicalSpace EReal.topologicalSpace) (Prod.mk.{0, 0} EReal EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) p))) (Filter.map.{0, 0} (Prod.{0, 0} Real Real) (Prod.{0, 0} EReal EReal) (fun (p : Prod.{0, 0} Real Real) => Prod.mk.{0, 0} EReal EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (Prod.fst.{0, 0} Real Real p)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (Prod.snd.{0, 0} Real Real p))) (nhds.{0} (Prod.{0, 0} Real Real) (Prod.topologicalSpace.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (Prod.mk.{0, 0} Real Real r p)))
but is expected to have type
  forall {r : Real} {p : Real}, Eq.{1} (Filter.{0} (Prod.{0, 0} EReal EReal)) (nhds.{0} (Prod.{0, 0} EReal EReal) (instTopologicalSpaceProd.{0, 0} EReal EReal EReal.instTopologicalSpaceEReal EReal.instTopologicalSpaceEReal) (Prod.mk.{0, 0} EReal EReal (Real.toEReal r) (Real.toEReal p))) (Filter.map.{0, 0} (Prod.{0, 0} Real Real) (Prod.{0, 0} EReal EReal) (fun (p : Prod.{0, 0} Real Real) => Prod.mk.{0, 0} EReal EReal (Real.toEReal (Prod.fst.{0, 0} Real Real p)) (Real.toEReal (Prod.snd.{0, 0} Real Real p))) (nhds.{0} (Prod.{0, 0} Real Real) (instTopologicalSpaceProd.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (Prod.mk.{0, 0} Real Real r p)))
Case conversion may be inaccurate. Consider using '#align ereal.nhds_coe_coe EReal.nhds_coe_coeₓ'. -/
theorem nhds_coe_coe {r p : ℝ} :
    𝓝 ((r : EReal), (p : EReal)) = (𝓝 (r, p)).map fun p : ℝ × ℝ => (p.1, p.2) :=
  ((openEmbedding_coe.Prod openEmbedding_coe).map_nhds_eq (r, p)).symm
#align ereal.nhds_coe_coe EReal.nhds_coe_coe

/- warning: ereal.tendsto_to_real -> EReal.tendsto_toReal is a dubious translation:
lean 3 declaration is
  forall {a : EReal}, (Ne.{1} EReal a (Top.top.{0} EReal EReal.hasTop)) -> (Ne.{1} EReal a (Bot.bot.{0} EReal EReal.hasBot)) -> (Filter.Tendsto.{0, 0} EReal Real EReal.toReal (nhds.{0} EReal EReal.topologicalSpace a) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (EReal.toReal a)))
but is expected to have type
  forall {a : EReal}, (Ne.{1} EReal a (Top.top.{0} EReal EReal.instTopEReal)) -> (Ne.{1} EReal a (Bot.bot.{0} EReal instERealBot)) -> (Filter.Tendsto.{0, 0} EReal Real EReal.toReal (nhds.{0} EReal EReal.instTopologicalSpaceEReal a) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (EReal.toReal a)))
Case conversion may be inaccurate. Consider using '#align ereal.tendsto_to_real EReal.tendsto_toRealₓ'. -/
theorem tendsto_toReal {a : EReal} (ha : a ≠ ⊤) (h'a : a ≠ ⊥) :
    Tendsto EReal.toReal (𝓝 a) (𝓝 a.toReal) :=
  by
  lift a to ℝ using And.intro ha h'a
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id
#align ereal.tendsto_to_real EReal.tendsto_toReal

/- warning: ereal.continuous_on_to_real -> EReal.continuousOn_toReal is a dubious translation:
lean 3 declaration is
  ContinuousOn.{0, 0} EReal Real EReal.topologicalSpace (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) EReal.toReal (HasCompl.compl.{0} (Set.{0} EReal) (BooleanAlgebra.toHasCompl.{0} (Set.{0} EReal) (Set.booleanAlgebra.{0} EReal)) (Insert.insert.{0, 0} EReal (Set.{0} EReal) (Set.hasInsert.{0} EReal) (Bot.bot.{0} EReal EReal.hasBot) (Singleton.singleton.{0, 0} EReal (Set.{0} EReal) (Set.hasSingleton.{0} EReal) (Top.top.{0} EReal EReal.hasTop))))
but is expected to have type
  ContinuousOn.{0, 0} EReal Real EReal.instTopologicalSpaceEReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) EReal.toReal (HasCompl.compl.{0} (Set.{0} EReal) (BooleanAlgebra.toHasCompl.{0} (Set.{0} EReal) (Set.instBooleanAlgebraSet.{0} EReal)) (Insert.insert.{0, 0} EReal (Set.{0} EReal) (Set.instInsertSet.{0} EReal) (Bot.bot.{0} EReal instERealBot) (Singleton.singleton.{0, 0} EReal (Set.{0} EReal) (Set.instSingletonSet.{0} EReal) (Top.top.{0} EReal EReal.instTopEReal))))
Case conversion may be inaccurate. Consider using '#align ereal.continuous_on_to_real EReal.continuousOn_toRealₓ'. -/
theorem continuousOn_toReal : ContinuousOn EReal.toReal ({⊥, ⊤}ᶜ : Set EReal) := fun a ha =>
  ContinuousAt.continuousWithinAt
    (tendsto_toReal
      (by
        simp [not_or] at ha
        exact ha.2)
      (by
        simp [not_or] at ha
        exact ha.1))
#align ereal.continuous_on_to_real EReal.continuousOn_toReal

/- warning: ereal.ne_bot_top_homeomorph_real -> EReal.neBotTopHomeomorphReal is a dubious translation:
lean 3 declaration is
  Homeomorph.{0, 0} (coeSort.{1, 2} (Set.{0} EReal) Type (Set.hasCoeToSort.{0} EReal) (HasCompl.compl.{0} (Set.{0} EReal) (BooleanAlgebra.toHasCompl.{0} (Set.{0} EReal) (Set.booleanAlgebra.{0} EReal)) (Insert.insert.{0, 0} EReal (Set.{0} EReal) (Set.hasInsert.{0} EReal) (Bot.bot.{0} EReal EReal.hasBot) (Singleton.singleton.{0, 0} EReal (Set.{0} EReal) (Set.hasSingleton.{0} EReal) (Top.top.{0} EReal EReal.hasTop))))) Real (Subtype.topologicalSpace.{0} EReal (fun (x : EReal) => Membership.Mem.{0, 0} EReal (Set.{0} EReal) (Set.hasMem.{0} EReal) x (HasCompl.compl.{0} (Set.{0} EReal) (BooleanAlgebra.toHasCompl.{0} (Set.{0} EReal) (Set.booleanAlgebra.{0} EReal)) (Insert.insert.{0, 0} EReal (Set.{0} EReal) (Set.hasInsert.{0} EReal) (Bot.bot.{0} EReal EReal.hasBot) (Singleton.singleton.{0, 0} EReal (Set.{0} EReal) (Set.hasSingleton.{0} EReal) (Top.top.{0} EReal EReal.hasTop))))) EReal.topologicalSpace) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
but is expected to have type
  Homeomorph.{0, 0} (Set.Elem.{0} EReal (HasCompl.compl.{0} (Set.{0} EReal) (BooleanAlgebra.toHasCompl.{0} (Set.{0} EReal) (Set.instBooleanAlgebraSet.{0} EReal)) (Insert.insert.{0, 0} EReal (Set.{0} EReal) (Set.instInsertSet.{0} EReal) (Bot.bot.{0} EReal instERealBot) (Singleton.singleton.{0, 0} EReal (Set.{0} EReal) (Set.instSingletonSet.{0} EReal) (Top.top.{0} EReal EReal.instTopEReal))))) Real (instTopologicalSpaceSubtype.{0} EReal (fun (x : EReal) => Membership.mem.{0, 0} EReal (Set.{0} EReal) (Set.instMembershipSet.{0} EReal) x (HasCompl.compl.{0} (Set.{0} EReal) (BooleanAlgebra.toHasCompl.{0} (Set.{0} EReal) (Set.instBooleanAlgebraSet.{0} EReal)) (Insert.insert.{0, 0} EReal (Set.{0} EReal) (Set.instInsertSet.{0} EReal) (Bot.bot.{0} EReal instERealBot) (Singleton.singleton.{0, 0} EReal (Set.{0} EReal) (Set.instSingletonSet.{0} EReal) (Top.top.{0} EReal EReal.instTopEReal))))) EReal.instTopologicalSpaceEReal) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
Case conversion may be inaccurate. Consider using '#align ereal.ne_bot_top_homeomorph_real EReal.neBotTopHomeomorphRealₓ'. -/
/-- The set of finite `ereal` numbers is homeomorphic to `ℝ`. -/
def neBotTopHomeomorphReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ₜ ℝ :=
  {
    neTopBotEquivReal with
    continuous_toFun := continuousOn_iff_continuous_restrict.1 continuousOn_toReal
    continuous_invFun := continuous_coe_real_ereal.subtype_mk _ }
#align ereal.ne_bot_top_homeomorph_real EReal.neBotTopHomeomorphReal

/-! ### ennreal coercion -/


/- warning: ereal.embedding_coe_ennreal -> EReal.embedding_coe_ennreal is a dubious translation:
lean 3 declaration is
  Embedding.{0, 0} ENNReal EReal ENNReal.topologicalSpace EReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))))
but is expected to have type
  Embedding.{0, 0} ENNReal EReal ENNReal.instTopologicalSpaceENNReal EReal.instTopologicalSpaceEReal ENNReal.toEReal
Case conversion may be inaccurate. Consider using '#align ereal.embedding_coe_ennreal EReal.embedding_coe_ennrealₓ'. -/
theorem embedding_coe_ennreal : Embedding (coe : ℝ≥0∞ → EReal) :=
  ⟨⟨by
      refine' le_antisymm _ _
      · rw [@OrderTopology.topology_eq_generate_intervals EReal _, ← coinduced_le_iff_le_induced]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        show IsOpen { b : ℝ≥0∞ | a < ↑b }
        · induction' a using EReal.rec with x
          · simp only [isOpen_univ, bot_lt_coe_ennreal, set_of_true]
          · rcases le_or_lt 0 x with (h | h)
            · have : (x : EReal) = ((id ⟨x, h⟩ : ℝ≥0) : ℝ≥0∞) := rfl
              rw [this]
              simp only [id.def, coe_ennreal_lt_coe_ennreal_iff]
              exact isOpen_Ioi
            · have : ∀ y : ℝ≥0∞, (x : EReal) < y := fun y =>
                (EReal.coe_lt_coe_iff.2 h).trans_le (coe_ennreal_nonneg _)
              simp only [this, isOpen_univ, set_of_true]
          · simp only [set_of_false, isOpen_empty, not_top_lt]
        show IsOpen { b : ℝ≥0∞ | ↑b < a }
        · induction' a using EReal.rec with x
          · simp only [not_lt_bot, set_of_false, isOpen_empty]
          · rcases le_or_lt 0 x with (h | h)
            · have : (x : EReal) = ((id ⟨x, h⟩ : ℝ≥0) : ℝ≥0∞) := rfl
              rw [this]
              simp only [id.def, coe_ennreal_lt_coe_ennreal_iff]
              exact isOpen_Iio
            · convert isOpen_empty
              apply eq_empty_iff_forall_not_mem.2 fun y hy => lt_irrefl (x : EReal) _
              exact ((EReal.coe_lt_coe_iff.2 h).trans_le (coe_ennreal_nonneg y)).trans hy
          · simp only [← coe_ennreal_top, coe_ennreal_lt_coe_ennreal_iff]
            exact isOpen_Iio
      · rw [@OrderTopology.topology_eq_generate_intervals ℝ≥0∞ _]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        exact ⟨Ioi a, isOpen_Ioi, by simp [Ioi]⟩
        exact ⟨Iio a, isOpen_Iio, by simp [Iio]⟩⟩, fun a b => by
    simp only [imp_self, coe_ennreal_eq_coe_ennreal_iff]⟩
#align ereal.embedding_coe_ennreal EReal.embedding_coe_ennreal

/- warning: ereal.tendsto_coe_ennreal -> EReal.tendsto_coe_ennreal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal}, Iff (Filter.Tendsto.{u1, 0} α EReal (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (m a)) f (nhds.{0} EReal EReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) a))) (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.topologicalSpace a))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal}, Iff (Filter.Tendsto.{u1, 0} α EReal (fun (a : α) => ENNReal.toEReal (m a)) f (nhds.{0} EReal EReal.instTopologicalSpaceEReal (ENNReal.toEReal a))) (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a))
Case conversion may be inaccurate. Consider using '#align ereal.tendsto_coe_ennreal EReal.tendsto_coe_ennrealₓ'. -/
@[norm_cast]
theorem tendsto_coe_ennreal {α : Type _} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe_ennreal.tendsto_nhds_iff.symm
#align ereal.tendsto_coe_ennreal EReal.tendsto_coe_ennreal

/- warning: continuous_coe_ennreal_ereal -> continuous_coe_ennreal_ereal is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} ENNReal EReal ENNReal.topologicalSpace EReal.topologicalSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))))
but is expected to have type
  Continuous.{0, 0} ENNReal EReal ENNReal.instTopologicalSpaceENNReal EReal.instTopologicalSpaceEReal ENNReal.toEReal
Case conversion may be inaccurate. Consider using '#align continuous_coe_ennreal_ereal continuous_coe_ennreal_erealₓ'. -/
theorem continuous_coe_ennreal_ereal : Continuous (coe : ℝ≥0∞ → EReal) :=
  embedding_coe_ennreal.Continuous
#align continuous_coe_ennreal_ereal continuous_coe_ennreal_ereal

/- warning: ereal.continuous_coe_ennreal_iff -> EReal.continuous_coe_ennreal_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> ENNReal}, Iff (Continuous.{u1, 0} α EReal _inst_1 EReal.topologicalSpace (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (f a))) (Continuous.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> ENNReal}, Iff (Continuous.{u1, 0} α EReal _inst_1 EReal.instTopologicalSpaceEReal (fun (a : α) => ENNReal.toEReal (f a))) (Continuous.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal f)
Case conversion may be inaccurate. Consider using '#align ereal.continuous_coe_ennreal_iff EReal.continuous_coe_ennreal_iffₓ'. -/
theorem continuous_coe_ennreal_iff {f : α → ℝ≥0∞} :
    (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  embedding_coe_ennreal.continuous_iff.symm
#align ereal.continuous_coe_ennreal_iff EReal.continuous_coe_ennreal_iff

/-! ### Neighborhoods of infinity -/


/- warning: ereal.nhds_top -> EReal.nhds_top is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} EReal) (nhds.{0} EReal EReal.topologicalSpace (Top.top.{0} EReal EReal.hasTop)) (iInf.{0, 1} (Filter.{0} EReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.completeLattice.{0} EReal))) EReal (fun (a : EReal) => iInf.{0, 0} (Filter.{0} EReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.completeLattice.{0} EReal))) (Ne.{1} EReal a (Top.top.{0} EReal EReal.hasTop)) (fun (H : Ne.{1} EReal a (Top.top.{0} EReal EReal.hasTop)) => Filter.principal.{0} EReal (Set.Ioi.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) a))))
but is expected to have type
  Eq.{1} (Filter.{0} EReal) (nhds.{0} EReal EReal.instTopologicalSpaceEReal (Top.top.{0} EReal EReal.instTopEReal)) (iInf.{0, 1} (Filter.{0} EReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.instCompleteLatticeFilter.{0} EReal))) EReal (fun (a : EReal) => iInf.{0, 0} (Filter.{0} EReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.instCompleteLatticeFilter.{0} EReal))) (Ne.{1} EReal a (Top.top.{0} EReal EReal.instTopEReal)) (fun (H : Ne.{1} EReal a (Top.top.{0} EReal EReal.instTopEReal)) => Filter.principal.{0} EReal (Set.Ioi.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) a))))
Case conversion may be inaccurate. Consider using '#align ereal.nhds_top EReal.nhds_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ≠ » «expr⊤»()) -/
theorem nhds_top : 𝓝 (⊤ : EReal) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp [lt_top_iff_ne_top, Ioi]
#align ereal.nhds_top EReal.nhds_top

/- warning: ereal.nhds_top' -> EReal.nhds_top' is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} EReal) (nhds.{0} EReal EReal.topologicalSpace (Top.top.{0} EReal EReal.hasTop)) (iInf.{0, 1} (Filter.{0} EReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.completeLattice.{0} EReal))) Real (fun (a : Real) => Filter.principal.{0} EReal (Set.Ioi.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) a))))
but is expected to have type
  Eq.{1} (Filter.{0} EReal) (nhds.{0} EReal EReal.instTopologicalSpaceEReal (Top.top.{0} EReal EReal.instTopEReal)) (iInf.{0, 1} (Filter.{0} EReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.instCompleteLatticeFilter.{0} EReal))) Real (fun (a : Real) => Filter.principal.{0} EReal (Set.Ioi.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (Real.toEReal a))))
Case conversion may be inaccurate. Consider using '#align ereal.nhds_top' EReal.nhds_top'ₓ'. -/
theorem nhds_top' : 𝓝 (⊤ : EReal) = ⨅ a : ℝ, 𝓟 (Ioi a) :=
  by
  rw [nhds_top]
  apply le_antisymm
  · exact iInf_mono' fun x => ⟨x, by simp⟩
  · refine' le_iInf fun r => le_iInf fun hr => _
    induction r using EReal.rec
    · exact (iInf_le _ 0).trans (by simp)
    · exact iInf_le _ _
    · simpa using hr
#align ereal.nhds_top' EReal.nhds_top'

/- warning: ereal.mem_nhds_top_iff -> EReal.mem_nhds_top_iff is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} EReal}, Iff (Membership.Mem.{0, 0} (Set.{0} EReal) (Filter.{0} EReal) (Filter.hasMem.{0} EReal) s (nhds.{0} EReal EReal.topologicalSpace (Top.top.{0} EReal EReal.hasTop))) (Exists.{1} Real (fun (y : Real) => HasSubset.Subset.{0} (Set.{0} EReal) (Set.hasSubset.{0} EReal) (Set.Ioi.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) y)) s))
but is expected to have type
  forall {s : Set.{0} EReal}, Iff (Membership.mem.{0, 0} (Set.{0} EReal) (Filter.{0} EReal) (instMembershipSetFilter.{0} EReal) s (nhds.{0} EReal EReal.instTopologicalSpaceEReal (Top.top.{0} EReal EReal.instTopEReal))) (Exists.{1} Real (fun (y : Real) => HasSubset.Subset.{0} (Set.{0} EReal) (Set.instHasSubsetSet.{0} EReal) (Set.Ioi.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (Real.toEReal y)) s))
Case conversion may be inaccurate. Consider using '#align ereal.mem_nhds_top_iff EReal.mem_nhds_top_iffₓ'. -/
theorem mem_nhds_top_iff {s : Set EReal} : s ∈ 𝓝 (⊤ : EReal) ↔ ∃ y : ℝ, Ioi (y : EReal) ⊆ s :=
  by
  rw [nhds_top', mem_infi_of_directed]
  · rfl
  exact fun x y => ⟨max x y, by simp [le_refl], by simp [le_refl]⟩
#align ereal.mem_nhds_top_iff EReal.mem_nhds_top_iff

/- warning: ereal.tendsto_nhds_top_iff_real -> EReal.tendsto_nhds_top_iff_real is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : α -> EReal} {f : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, 0} α EReal m f (nhds.{0} EReal EReal.topologicalSpace (Top.top.{0} EReal EReal.hasTop))) (forall (x : Real), Filter.Eventually.{u1} α (fun (a : α) => LT.lt.{0} EReal (Preorder.toHasLt.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (m a)) f)
but is expected to have type
  forall {α : Type.{u1}} {m : α -> EReal} {f : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, 0} α EReal m f (nhds.{0} EReal EReal.instTopologicalSpaceEReal (Top.top.{0} EReal EReal.instTopEReal))) (forall (x : Real), Filter.Eventually.{u1} α (fun (a : α) => LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Real.toEReal x) (m a)) f)
Case conversion may be inaccurate. Consider using '#align ereal.tendsto_nhds_top_iff_real EReal.tendsto_nhds_top_iff_realₓ'. -/
theorem tendsto_nhds_top_iff_real {α : Type _} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠ a in f, ↑x < m a := by
  simp only [nhds_top', mem_Ioi, tendsto_infi, tendsto_principal]
#align ereal.tendsto_nhds_top_iff_real EReal.tendsto_nhds_top_iff_real

/- warning: ereal.nhds_bot -> EReal.nhds_bot is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} EReal) (nhds.{0} EReal EReal.topologicalSpace (Bot.bot.{0} EReal EReal.hasBot)) (iInf.{0, 1} (Filter.{0} EReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.completeLattice.{0} EReal))) EReal (fun (a : EReal) => iInf.{0, 0} (Filter.{0} EReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.completeLattice.{0} EReal))) (Ne.{1} EReal a (Bot.bot.{0} EReal EReal.hasBot)) (fun (H : Ne.{1} EReal a (Bot.bot.{0} EReal EReal.hasBot)) => Filter.principal.{0} EReal (Set.Iio.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) a))))
but is expected to have type
  Eq.{1} (Filter.{0} EReal) (nhds.{0} EReal EReal.instTopologicalSpaceEReal (Bot.bot.{0} EReal instERealBot)) (iInf.{0, 1} (Filter.{0} EReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.instCompleteLatticeFilter.{0} EReal))) EReal (fun (a : EReal) => iInf.{0, 0} (Filter.{0} EReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.instCompleteLatticeFilter.{0} EReal))) (Ne.{1} EReal a (Bot.bot.{0} EReal instERealBot)) (fun (H : Ne.{1} EReal a (Bot.bot.{0} EReal instERealBot)) => Filter.principal.{0} EReal (Set.Iio.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) a))))
Case conversion may be inaccurate. Consider using '#align ereal.nhds_bot EReal.nhds_botₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ≠ » «expr⊥»()) -/
theorem nhds_bot : 𝓝 (⊥ : EReal) = ⨅ (a) (_ : a ≠ ⊥), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp [bot_lt_iff_ne_bot]
#align ereal.nhds_bot EReal.nhds_bot

/- warning: ereal.nhds_bot' -> EReal.nhds_bot' is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} EReal) (nhds.{0} EReal EReal.topologicalSpace (Bot.bot.{0} EReal EReal.hasBot)) (iInf.{0, 1} (Filter.{0} EReal) (ConditionallyCompleteLattice.toHasInf.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.completeLattice.{0} EReal))) Real (fun (a : Real) => Filter.principal.{0} EReal (Set.Iio.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) a))))
but is expected to have type
  Eq.{1} (Filter.{0} EReal) (nhds.{0} EReal EReal.instTopologicalSpaceEReal (Bot.bot.{0} EReal instERealBot)) (iInf.{0, 1} (Filter.{0} EReal) (ConditionallyCompleteLattice.toInfSet.{0} (Filter.{0} EReal) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} EReal) (Filter.instCompleteLatticeFilter.{0} EReal))) Real (fun (a : Real) => Filter.principal.{0} EReal (Set.Iio.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (Real.toEReal a))))
Case conversion may be inaccurate. Consider using '#align ereal.nhds_bot' EReal.nhds_bot'ₓ'. -/
theorem nhds_bot' : 𝓝 (⊥ : EReal) = ⨅ a : ℝ, 𝓟 (Iio a) :=
  by
  rw [nhds_bot]
  apply le_antisymm
  · exact iInf_mono' fun x => ⟨x, by simp⟩
  · refine' le_iInf fun r => le_iInf fun hr => _
    induction r using EReal.rec
    · simpa using hr
    · exact iInf_le _ _
    · exact (iInf_le _ 0).trans (by simp)
#align ereal.nhds_bot' EReal.nhds_bot'

/- warning: ereal.mem_nhds_bot_iff -> EReal.mem_nhds_bot_iff is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} EReal}, Iff (Membership.Mem.{0, 0} (Set.{0} EReal) (Filter.{0} EReal) (Filter.hasMem.{0} EReal) s (nhds.{0} EReal EReal.topologicalSpace (Bot.bot.{0} EReal EReal.hasBot))) (Exists.{1} Real (fun (y : Real) => HasSubset.Subset.{0} (Set.{0} EReal) (Set.hasSubset.{0} EReal) (Set.Iio.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) y)) s))
but is expected to have type
  forall {s : Set.{0} EReal}, Iff (Membership.mem.{0, 0} (Set.{0} EReal) (Filter.{0} EReal) (instMembershipSetFilter.{0} EReal) s (nhds.{0} EReal EReal.instTopologicalSpaceEReal (Bot.bot.{0} EReal instERealBot))) (Exists.{1} Real (fun (y : Real) => HasSubset.Subset.{0} (Set.{0} EReal) (Set.instHasSubsetSet.{0} EReal) (Set.Iio.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (Real.toEReal y)) s))
Case conversion may be inaccurate. Consider using '#align ereal.mem_nhds_bot_iff EReal.mem_nhds_bot_iffₓ'. -/
theorem mem_nhds_bot_iff {s : Set EReal} : s ∈ 𝓝 (⊥ : EReal) ↔ ∃ y : ℝ, Iio (y : EReal) ⊆ s :=
  by
  rw [nhds_bot', mem_infi_of_directed]
  · rfl
  exact fun x y => ⟨min x y, by simp [le_refl], by simp [le_refl]⟩
#align ereal.mem_nhds_bot_iff EReal.mem_nhds_bot_iff

/- warning: ereal.tendsto_nhds_bot_iff_real -> EReal.tendsto_nhds_bot_iff_real is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : α -> EReal} {f : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, 0} α EReal m f (nhds.{0} EReal EReal.topologicalSpace (Bot.bot.{0} EReal EReal.hasBot))) (forall (x : Real), Filter.Eventually.{u1} α (fun (a : α) => LT.lt.{0} EReal (Preorder.toHasLt.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (m a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) f)
but is expected to have type
  forall {α : Type.{u1}} {m : α -> EReal} {f : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, 0} α EReal m f (nhds.{0} EReal EReal.instTopologicalSpaceEReal (Bot.bot.{0} EReal instERealBot))) (forall (x : Real), Filter.Eventually.{u1} α (fun (a : α) => LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (m a) (Real.toEReal x)) f)
Case conversion may be inaccurate. Consider using '#align ereal.tendsto_nhds_bot_iff_real EReal.tendsto_nhds_bot_iff_realₓ'. -/
theorem tendsto_nhds_bot_iff_real {α : Type _} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊥) ↔ ∀ x : ℝ, ∀ᶠ a in f, m a < x := by
  simp only [nhds_bot', mem_Iio, tendsto_infi, tendsto_principal]
#align ereal.tendsto_nhds_bot_iff_real EReal.tendsto_nhds_bot_iff_real

/-! ### Continuity of addition -/


/- warning: ereal.continuous_at_add_coe_coe -> EReal.continuousAt_add_coe_coe is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (Prod.topologicalSpace.{0, 0} EReal EReal EReal.topologicalSpace EReal.topologicalSpace) EReal.topologicalSpace (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) b))
but is expected to have type
  forall (a : Real) (b : Real), ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (instTopologicalSpaceProd.{0, 0} EReal EReal EReal.instTopologicalSpaceEReal EReal.instTopologicalSpaceEReal) EReal.instTopologicalSpaceEReal (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal (Real.toEReal a) (Real.toEReal b))
Case conversion may be inaccurate. Consider using '#align ereal.continuous_at_add_coe_coe EReal.continuousAt_add_coe_coeₓ'. -/
theorem continuousAt_add_coe_coe (a b : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, b) := by
  simp only [ContinuousAt, nhds_coe_coe, ← coe_add, tendsto_map'_iff, (· ∘ ·), tendsto_coe,
    tendsto_add]
#align ereal.continuous_at_add_coe_coe EReal.continuousAt_add_coe_coe

/- warning: ereal.continuous_at_add_top_coe -> EReal.continuousAt_add_top_coe is a dubious translation:
lean 3 declaration is
  forall (a : Real), ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (Prod.topologicalSpace.{0, 0} EReal EReal EReal.topologicalSpace EReal.topologicalSpace) EReal.topologicalSpace (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal (Top.top.{0} EReal EReal.hasTop) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) a))
but is expected to have type
  forall (a : Real), ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (instTopologicalSpaceProd.{0, 0} EReal EReal EReal.instTopologicalSpaceEReal EReal.instTopologicalSpaceEReal) EReal.instTopologicalSpaceEReal (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal (Top.top.{0} EReal EReal.instTopEReal) (Real.toEReal a))
Case conversion may be inaccurate. Consider using '#align ereal.continuous_at_add_top_coe EReal.continuousAt_add_top_coeₓ'. -/
theorem continuousAt_add_top_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, a) :=
  by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_coe, nhds_prod_eq]
  intro r
  rw [eventually_prod_iff]
  refine'
    ⟨fun z => ((r - (a - 1) : ℝ) : EReal) < z, Ioi_mem_nhds (coe_lt_top _), fun z =>
      ((a - 1 : ℝ) : EReal) < z, Ioi_mem_nhds (by simp [-EReal.coe_sub]), fun x hx y hy => _⟩
  dsimp
  convert add_lt_add hx hy
  simp
#align ereal.continuous_at_add_top_coe EReal.continuousAt_add_top_coe

/- warning: ereal.continuous_at_add_coe_top -> EReal.continuousAt_add_coe_top is a dubious translation:
lean 3 declaration is
  forall (a : Real), ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (Prod.topologicalSpace.{0, 0} EReal EReal EReal.topologicalSpace EReal.topologicalSpace) EReal.topologicalSpace (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) a) (Top.top.{0} EReal EReal.hasTop))
but is expected to have type
  forall (a : Real), ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (instTopologicalSpaceProd.{0, 0} EReal EReal EReal.instTopologicalSpaceEReal EReal.instTopologicalSpaceEReal) EReal.instTopologicalSpaceEReal (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal (Real.toEReal a) (Top.top.{0} EReal EReal.instTopEReal))
Case conversion may be inaccurate. Consider using '#align ereal.continuous_at_add_coe_top EReal.continuousAt_add_coe_topₓ'. -/
theorem continuousAt_add_coe_top (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊤) :=
  by
  change ContinuousAt ((fun p : EReal × EReal => p.2 + p.1) ∘ Prod.swap) (a, ⊤)
  apply ContinuousAt.comp _ continuous_swap.continuous_at
  simp_rw [add_comm]
  exact continuous_at_add_top_coe a
#align ereal.continuous_at_add_coe_top EReal.continuousAt_add_coe_top

/- warning: ereal.continuous_at_add_top_top -> EReal.continuousAt_add_top_top is a dubious translation:
lean 3 declaration is
  ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (Prod.topologicalSpace.{0, 0} EReal EReal EReal.topologicalSpace EReal.topologicalSpace) EReal.topologicalSpace (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal (Top.top.{0} EReal EReal.hasTop) (Top.top.{0} EReal EReal.hasTop))
but is expected to have type
  ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (instTopologicalSpaceProd.{0, 0} EReal EReal EReal.instTopologicalSpaceEReal EReal.instTopologicalSpaceEReal) EReal.instTopologicalSpaceEReal (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal (Top.top.{0} EReal EReal.instTopEReal) (Top.top.{0} EReal EReal.instTopEReal))
Case conversion may be inaccurate. Consider using '#align ereal.continuous_at_add_top_top EReal.continuousAt_add_top_topₓ'. -/
theorem continuousAt_add_top_top : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, ⊤) :=
  by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_top, nhds_prod_eq]
  intro r
  rw [eventually_prod_iff]
  refine'
    ⟨fun z => (r : EReal) < z, Ioi_mem_nhds (coe_lt_top _), fun z => ((0 : ℝ) : EReal) < z,
      Ioi_mem_nhds (by simp [zero_lt_one]), fun x hx y hy => _⟩
  dsimp
  convert add_lt_add hx hy
  simp
#align ereal.continuous_at_add_top_top EReal.continuousAt_add_top_top

/- warning: ereal.continuous_at_add_bot_coe -> EReal.continuousAt_add_bot_coe is a dubious translation:
lean 3 declaration is
  forall (a : Real), ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (Prod.topologicalSpace.{0, 0} EReal EReal EReal.topologicalSpace EReal.topologicalSpace) EReal.topologicalSpace (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal (Bot.bot.{0} EReal EReal.hasBot) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) a))
but is expected to have type
  forall (a : Real), ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (instTopologicalSpaceProd.{0, 0} EReal EReal EReal.instTopologicalSpaceEReal EReal.instTopologicalSpaceEReal) EReal.instTopologicalSpaceEReal (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal (Bot.bot.{0} EReal instERealBot) (Real.toEReal a))
Case conversion may be inaccurate. Consider using '#align ereal.continuous_at_add_bot_coe EReal.continuousAt_add_bot_coeₓ'. -/
theorem continuousAt_add_bot_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, a) :=
  by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, nhds_prod_eq, bot_add]
  intro r
  rw [eventually_prod_iff]
  refine'
    ⟨fun z => z < ((r - (a + 1) : ℝ) : EReal), Iio_mem_nhds (bot_lt_coe _), fun z =>
      z < ((a + 1 : ℝ) : EReal), Iio_mem_nhds (by simp [-coe_add, zero_lt_one]), fun x hx y hy => _⟩
  convert add_lt_add hx hy
  rw [sub_add_cancel]
#align ereal.continuous_at_add_bot_coe EReal.continuousAt_add_bot_coe

/- warning: ereal.continuous_at_add_coe_bot -> EReal.continuousAt_add_coe_bot is a dubious translation:
lean 3 declaration is
  forall (a : Real), ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (Prod.topologicalSpace.{0, 0} EReal EReal EReal.topologicalSpace EReal.topologicalSpace) EReal.topologicalSpace (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) a) (Bot.bot.{0} EReal EReal.hasBot))
but is expected to have type
  forall (a : Real), ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (instTopologicalSpaceProd.{0, 0} EReal EReal EReal.instTopologicalSpaceEReal EReal.instTopologicalSpaceEReal) EReal.instTopologicalSpaceEReal (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal (Real.toEReal a) (Bot.bot.{0} EReal instERealBot))
Case conversion may be inaccurate. Consider using '#align ereal.continuous_at_add_coe_bot EReal.continuousAt_add_coe_botₓ'. -/
theorem continuousAt_add_coe_bot (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊥) :=
  by
  change ContinuousAt ((fun p : EReal × EReal => p.2 + p.1) ∘ Prod.swap) (a, ⊥)
  apply ContinuousAt.comp _ continuous_swap.continuous_at
  simp_rw [add_comm]
  exact continuous_at_add_bot_coe a
#align ereal.continuous_at_add_coe_bot EReal.continuousAt_add_coe_bot

/- warning: ereal.continuous_at_add_bot_bot -> EReal.continuousAt_add_bot_bot is a dubious translation:
lean 3 declaration is
  ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (Prod.topologicalSpace.{0, 0} EReal EReal EReal.topologicalSpace EReal.topologicalSpace) EReal.topologicalSpace (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal (Bot.bot.{0} EReal EReal.hasBot) (Bot.bot.{0} EReal EReal.hasBot))
but is expected to have type
  ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (instTopologicalSpaceProd.{0, 0} EReal EReal EReal.instTopologicalSpaceEReal EReal.instTopologicalSpaceEReal) EReal.instTopologicalSpaceEReal (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) (Prod.mk.{0, 0} EReal EReal (Bot.bot.{0} EReal instERealBot) (Bot.bot.{0} EReal instERealBot))
Case conversion may be inaccurate. Consider using '#align ereal.continuous_at_add_bot_bot EReal.continuousAt_add_bot_botₓ'. -/
theorem continuousAt_add_bot_bot : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, ⊥) :=
  by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, nhds_prod_eq, bot_add]
  intro r
  rw [eventually_prod_iff]
  refine'
    ⟨fun z => z < r, Iio_mem_nhds (bot_lt_coe _), fun z => z < 0, Iio_mem_nhds (bot_lt_coe _),
      fun x hx y hy => _⟩
  dsimp
  convert add_lt_add hx hy
  simp
#align ereal.continuous_at_add_bot_bot EReal.continuousAt_add_bot_bot

/- warning: ereal.continuous_at_add -> EReal.continuousAt_add is a dubious translation:
lean 3 declaration is
  forall {p : Prod.{0, 0} EReal EReal}, (Or (Ne.{1} EReal (Prod.fst.{0, 0} EReal EReal p) (Top.top.{0} EReal EReal.hasTop)) (Ne.{1} EReal (Prod.snd.{0, 0} EReal EReal p) (Bot.bot.{0} EReal EReal.hasBot))) -> (Or (Ne.{1} EReal (Prod.fst.{0, 0} EReal EReal p) (Bot.bot.{0} EReal EReal.hasBot)) (Ne.{1} EReal (Prod.snd.{0, 0} EReal EReal p) (Top.top.{0} EReal EReal.hasTop))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (Prod.topologicalSpace.{0, 0} EReal EReal EReal.topologicalSpace EReal.topologicalSpace) EReal.topologicalSpace (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) p)
but is expected to have type
  forall {p : Prod.{0, 0} EReal EReal}, (Or (Ne.{1} EReal (Prod.fst.{0, 0} EReal EReal p) (Top.top.{0} EReal EReal.instTopEReal)) (Ne.{1} EReal (Prod.snd.{0, 0} EReal EReal p) (Bot.bot.{0} EReal instERealBot))) -> (Or (Ne.{1} EReal (Prod.fst.{0, 0} EReal EReal p) (Bot.bot.{0} EReal instERealBot)) (Ne.{1} EReal (Prod.snd.{0, 0} EReal EReal p) (Top.top.{0} EReal EReal.instTopEReal))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} EReal EReal) EReal (instTopologicalSpaceProd.{0, 0} EReal EReal EReal.instTopologicalSpaceEReal EReal.instTopologicalSpaceEReal) EReal.instTopologicalSpaceEReal (fun (p : Prod.{0, 0} EReal EReal) => HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Prod.fst.{0, 0} EReal EReal p) (Prod.snd.{0, 0} EReal EReal p)) p)
Case conversion may be inaccurate. Consider using '#align ereal.continuous_at_add EReal.continuousAt_addₓ'. -/
/-- The addition on `ereal` is continuous except where it doesn't make sense (i.e., at `(⊥, ⊤)`
and at `(⊤, ⊥)`). -/
theorem continuousAt_add {p : EReal × EReal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊥) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊤) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) p :=
  by
  rcases p with ⟨x, y⟩
  induction x using EReal.rec <;> induction y using EReal.rec
  · exact continuous_at_add_bot_bot
  · exact continuous_at_add_bot_coe _
  · simpa using h'
  · exact continuous_at_add_coe_bot _
  · exact continuous_at_add_coe_coe _ _
  · exact continuous_at_add_coe_top _
  · simpa using h
  · exact continuous_at_add_top_coe _
  · exact continuous_at_add_top_top
#align ereal.continuous_at_add EReal.continuousAt_add

/-! ### Negation-/


/- warning: ereal.neg_homeo -> EReal.negHomeo is a dubious translation:
lean 3 declaration is
  Homeomorph.{0, 0} EReal EReal EReal.topologicalSpace EReal.topologicalSpace
but is expected to have type
  Homeomorph.{0, 0} EReal EReal EReal.instTopologicalSpaceEReal EReal.instTopologicalSpaceEReal
Case conversion may be inaccurate. Consider using '#align ereal.neg_homeo EReal.negHomeoₓ'. -/
/-- Negation on `ereal` as a homeomorphism -/
def negHomeo : EReal ≃ₜ EReal :=
  negOrderIso.toHomeomorph
#align ereal.neg_homeo EReal.negHomeo

/- warning: ereal.continuous_neg -> EReal.continuous_neg is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} EReal EReal EReal.topologicalSpace EReal.topologicalSpace (fun (x : EReal) => Neg.neg.{0} EReal EReal.hasNeg x)
but is expected to have type
  Continuous.{0, 0} EReal EReal EReal.instTopologicalSpaceEReal EReal.instTopologicalSpaceEReal (fun (x : EReal) => Neg.neg.{0} EReal EReal.instNegEReal x)
Case conversion may be inaccurate. Consider using '#align ereal.continuous_neg EReal.continuous_negₓ'. -/
theorem continuous_neg : Continuous fun x : EReal => -x :=
  negHomeo.Continuous
#align ereal.continuous_neg EReal.continuous_neg

end EReal

