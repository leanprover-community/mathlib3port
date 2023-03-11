/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module topology.instances.rat
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.Basic
import Mathbin.Topology.Algebra.Order.Archimedean
import Mathbin.Topology.Instances.Int
import Mathbin.Topology.Instances.Nat
import Mathbin.Topology.Instances.Real

/-!
# Topology on the ratonal numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The structure of a metric space on `ℚ` is introduced in this file, induced from `ℝ`.
-/


open Metric Set Filter

namespace Rat

-- without the `by exact` this is noncomputable
instance : MetricSpace ℚ :=
  MetricSpace.induced coe Rat.cast_injective Real.metricSpace

/- warning: rat.dist_eq -> Rat.dist_eq is a dubious translation:
lean 3 declaration is
  forall (x : Rat) (y : Rat), Eq.{1} Real (Dist.dist.{0} Rat (PseudoMetricSpace.toHasDist.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) x y) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) y)))
but is expected to have type
  forall (x : Rat) (y : Rat), Eq.{1} Real (Dist.dist.{0} Rat (PseudoMetricSpace.toDist.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) x y) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Rat.cast.{0} Real Real.ratCast x) (Rat.cast.{0} Real Real.ratCast y)))
Case conversion may be inaccurate. Consider using '#align rat.dist_eq Rat.dist_eqₓ'. -/
theorem dist_eq (x y : ℚ) : dist x y = |x - y| :=
  rfl
#align rat.dist_eq Rat.dist_eq

/- warning: rat.dist_cast -> Rat.dist_cast is a dubious translation:
lean 3 declaration is
  forall (x : Rat) (y : Rat), Eq.{1} Real (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) y)) (Dist.dist.{0} Rat (PseudoMetricSpace.toHasDist.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) x y)
but is expected to have type
  forall (x : Rat) (y : Rat), Eq.{1} Real (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) (Rat.cast.{0} Real Real.ratCast x) (Rat.cast.{0} Real Real.ratCast y)) (Dist.dist.{0} Rat (PseudoMetricSpace.toDist.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) x y)
Case conversion may be inaccurate. Consider using '#align rat.dist_cast Rat.dist_castₓ'. -/
@[norm_cast, simp]
theorem dist_cast (x y : ℚ) : dist (x : ℝ) y = dist x y :=
  rfl
#align rat.dist_cast Rat.dist_cast

/- warning: rat.uniform_continuous_coe_real -> Rat.uniformContinuous_coe_real is a dubious translation:
lean 3 declaration is
  UniformContinuous.{0, 0} Rat Real (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))))
but is expected to have type
  UniformContinuous.{0, 0} Rat Real (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (Rat.cast.{0} Real Real.ratCast)
Case conversion may be inaccurate. Consider using '#align rat.uniform_continuous_coe_real Rat.uniformContinuous_coe_realₓ'. -/
theorem uniformContinuous_coe_real : UniformContinuous (coe : ℚ → ℝ) :=
  uniformContinuous_comap
#align rat.uniform_continuous_coe_real Rat.uniformContinuous_coe_real

/- warning: rat.uniform_embedding_coe_real -> Rat.uniformEmbedding_coe_real is a dubious translation:
lean 3 declaration is
  UniformEmbedding.{0, 0} Rat Real (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))))
but is expected to have type
  UniformEmbedding.{0, 0} Rat Real (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (Rat.cast.{0} Real Real.ratCast)
Case conversion may be inaccurate. Consider using '#align rat.uniform_embedding_coe_real Rat.uniformEmbedding_coe_realₓ'. -/
theorem uniformEmbedding_coe_real : UniformEmbedding (coe : ℚ → ℝ) :=
  uniformEmbedding_comap Rat.cast_injective
#align rat.uniform_embedding_coe_real Rat.uniformEmbedding_coe_real

/- warning: rat.dense_embedding_coe_real -> Rat.denseEmbedding_coe_real is a dubious translation:
lean 3 declaration is
  DenseEmbedding.{0, 0} Rat Real (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))))
but is expected to have type
  DenseEmbedding.{0, 0} Rat Real (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Rat.cast.{0} Real Real.ratCast)
Case conversion may be inaccurate. Consider using '#align rat.dense_embedding_coe_real Rat.denseEmbedding_coe_realₓ'. -/
theorem denseEmbedding_coe_real : DenseEmbedding (coe : ℚ → ℝ) :=
  uniformEmbedding_coe_real.DenseEmbedding Rat.denseRange_cast
#align rat.dense_embedding_coe_real Rat.denseEmbedding_coe_real

/- warning: rat.embedding_coe_real -> Rat.embedding_coe_real is a dubious translation:
lean 3 declaration is
  Embedding.{0, 0} Rat Real (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))))
but is expected to have type
  Embedding.{0, 0} Rat Real (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Rat.cast.{0} Real Real.ratCast)
Case conversion may be inaccurate. Consider using '#align rat.embedding_coe_real Rat.embedding_coe_realₓ'. -/
theorem embedding_coe_real : Embedding (coe : ℚ → ℝ) :=
  denseEmbedding_coe_real.toEmbedding
#align rat.embedding_coe_real Rat.embedding_coe_real

/- warning: rat.continuous_coe_real -> Rat.continuous_coe_real is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} Rat Real (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))))
but is expected to have type
  Continuous.{0, 0} Rat Real (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Rat.cast.{0} Real Real.ratCast)
Case conversion may be inaccurate. Consider using '#align rat.continuous_coe_real Rat.continuous_coe_realₓ'. -/
theorem continuous_coe_real : Continuous (coe : ℚ → ℝ) :=
  uniformContinuous_coe_real.Continuous
#align rat.continuous_coe_real Rat.continuous_coe_real

end Rat

/- warning: nat.dist_cast_rat -> Nat.dist_cast_rat is a dubious translation:
lean 3 declaration is
  forall (x : Nat) (y : Nat), Eq.{1} Real (Dist.dist.{0} Rat (PseudoMetricSpace.toHasDist.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) y)) (Dist.dist.{0} Nat Nat.hasDist x y)
but is expected to have type
  forall (x : Nat) (y : Nat), Eq.{1} Real (Dist.dist.{0} Rat (PseudoMetricSpace.toDist.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) x) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) y)) (Dist.dist.{0} Nat Nat.instDistNat x y)
Case conversion may be inaccurate. Consider using '#align nat.dist_cast_rat Nat.dist_cast_ratₓ'. -/
@[norm_cast, simp]
theorem Nat.dist_cast_rat (x y : ℕ) : dist (x : ℚ) y = dist x y := by
  rw [← Nat.dist_cast_real, ← Rat.dist_cast] <;> congr 1 <;> norm_cast
#align nat.dist_cast_rat Nat.dist_cast_rat

/- warning: nat.uniform_embedding_coe_rat -> Nat.uniformEmbedding_coe_rat is a dubious translation:
lean 3 declaration is
  UniformEmbedding.{0, 0} Nat Rat Nat.uniformSpace (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))))
but is expected to have type
  UniformEmbedding.{0, 0} Nat Rat instUniformSpaceNat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))))
Case conversion may be inaccurate. Consider using '#align nat.uniform_embedding_coe_rat Nat.uniformEmbedding_coe_ratₓ'. -/
theorem Nat.uniformEmbedding_coe_rat : UniformEmbedding (coe : ℕ → ℚ) :=
  uniformEmbedding_bot_of_pairwise_le_dist zero_lt_one <| by simpa using Nat.pairwise_one_le_dist
#align nat.uniform_embedding_coe_rat Nat.uniformEmbedding_coe_rat

/- warning: nat.closed_embedding_coe_rat -> Nat.closedEmbedding_coe_rat is a dubious translation:
lean 3 declaration is
  ClosedEmbedding.{0, 0} Nat Rat Nat.topologicalSpace (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))))
but is expected to have type
  ClosedEmbedding.{0, 0} Nat Rat instTopologicalSpaceNat (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat))) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))))
Case conversion may be inaccurate. Consider using '#align nat.closed_embedding_coe_rat Nat.closedEmbedding_coe_ratₓ'. -/
theorem Nat.closedEmbedding_coe_rat : ClosedEmbedding (coe : ℕ → ℚ) :=
  closedEmbedding_of_pairwise_le_dist zero_lt_one <| by simpa using Nat.pairwise_one_le_dist
#align nat.closed_embedding_coe_rat Nat.closedEmbedding_coe_rat

/- warning: int.dist_cast_rat -> Int.dist_cast_rat is a dubious translation:
lean 3 declaration is
  forall (x : Int) (y : Int), Eq.{1} Real (Dist.dist.{0} Rat (PseudoMetricSpace.toHasDist.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) y)) (Dist.dist.{0} Int Int.hasDist x y)
but is expected to have type
  forall (x : Int) (y : Int), Eq.{1} Real (Dist.dist.{0} Rat (PseudoMetricSpace.toDist.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (Int.cast.{0} Rat Rat.instIntCastRat x) (Int.cast.{0} Rat Rat.instIntCastRat y)) (Dist.dist.{0} Int Int.instDistInt x y)
Case conversion may be inaccurate. Consider using '#align int.dist_cast_rat Int.dist_cast_ratₓ'. -/
@[norm_cast, simp]
theorem Int.dist_cast_rat (x y : ℤ) : dist (x : ℚ) y = dist x y := by
  rw [← Int.dist_cast_real, ← Rat.dist_cast] <;> congr 1 <;> norm_cast
#align int.dist_cast_rat Int.dist_cast_rat

/- warning: int.uniform_embedding_coe_rat -> Int.uniformEmbedding_coe_rat is a dubious translation:
lean 3 declaration is
  UniformEmbedding.{0, 0} Int Rat Int.uniformSpace (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))))
but is expected to have type
  UniformEmbedding.{0, 0} Int Rat instUniformSpaceInt (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (Int.cast.{0} Rat Rat.instIntCastRat)
Case conversion may be inaccurate. Consider using '#align int.uniform_embedding_coe_rat Int.uniformEmbedding_coe_ratₓ'. -/
theorem Int.uniformEmbedding_coe_rat : UniformEmbedding (coe : ℤ → ℚ) :=
  uniformEmbedding_bot_of_pairwise_le_dist zero_lt_one <| by simpa using Int.pairwise_one_le_dist
#align int.uniform_embedding_coe_rat Int.uniformEmbedding_coe_rat

/- warning: int.closed_embedding_coe_rat -> Int.closedEmbedding_coe_rat is a dubious translation:
lean 3 declaration is
  ClosedEmbedding.{0, 0} Int Rat Int.topologicalSpace (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))))
but is expected to have type
  ClosedEmbedding.{0, 0} Int Rat instTopologicalSpaceInt (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat))) (Int.cast.{0} Rat Rat.instIntCastRat)
Case conversion may be inaccurate. Consider using '#align int.closed_embedding_coe_rat Int.closedEmbedding_coe_ratₓ'. -/
theorem Int.closedEmbedding_coe_rat : ClosedEmbedding (coe : ℤ → ℚ) :=
  closedEmbedding_of_pairwise_le_dist zero_lt_one <| by simpa using Int.pairwise_one_le_dist
#align int.closed_embedding_coe_rat Int.closedEmbedding_coe_rat

namespace Rat

instance : NoncompactSpace ℚ :=
  Int.closedEmbedding_coe_rat.NoncompactSpace

/- warning: rat.uniform_continuous_add -> Rat.uniformContinuous_add is a dubious translation:
lean 3 declaration is
  UniformContinuous.{0, 0} (Prod.{0, 0} Rat Rat) Rat (Prod.uniformSpace.{0, 0} Rat Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace))) (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) (fun (p : Prod.{0, 0} Rat Rat) => HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) (Prod.fst.{0, 0} Rat Rat p) (Prod.snd.{0, 0} Rat Rat p))
but is expected to have type
  UniformContinuous.{0, 0} (Prod.{0, 0} Rat Rat) Rat (instUniformSpaceProd.{0, 0} Rat Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat))) (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (fun (p : Prod.{0, 0} Rat Rat) => HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) (Prod.fst.{0, 0} Rat Rat p) (Prod.snd.{0, 0} Rat Rat p))
Case conversion may be inaccurate. Consider using '#align rat.uniform_continuous_add Rat.uniformContinuous_addₓ'. -/
-- TODO(Mario): Find a way to use rat_add_continuous_lemma
theorem uniformContinuous_add : UniformContinuous fun p : ℚ × ℚ => p.1 + p.2 :=
  Rat.uniformEmbedding_coe_real.to_uniformInducing.uniformContinuous_iff.2 <| by
    simp only [(· ∘ ·), Rat.cast_add] <;>
      exact
        real.uniform_continuous_add.comp
          (rat.uniform_continuous_coe_real.prod_map Rat.uniformContinuous_coe_real)
#align rat.uniform_continuous_add Rat.uniformContinuous_add

/- warning: rat.uniform_continuous_neg -> Rat.uniformContinuous_neg is a dubious translation:
lean 3 declaration is
  UniformContinuous.{0, 0} Rat Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) (Neg.neg.{0} Rat Rat.hasNeg)
but is expected to have type
  UniformContinuous.{0, 0} Rat Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (Neg.neg.{0} Rat Rat.instNegRat)
Case conversion may be inaccurate. Consider using '#align rat.uniform_continuous_neg Rat.uniformContinuous_negₓ'. -/
theorem uniformContinuous_neg : UniformContinuous (@Neg.neg ℚ _) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun a b h => by rw [dist_comm] at h <;> simpa [Rat.dist_eq] using h⟩
#align rat.uniform_continuous_neg Rat.uniformContinuous_neg

instance : UniformAddGroup ℚ :=
  UniformAddGroup.mk' Rat.uniformContinuous_add Rat.uniformContinuous_neg

instance : TopologicalAddGroup ℚ := by infer_instance

instance : OrderTopology ℚ :=
  induced_orderTopology _ (fun x y => Rat.cast_lt) (@exists_rat_btwn _ _ _)

/- warning: rat.uniform_continuous_abs -> Rat.uniformContinuous_abs is a dubious translation:
lean 3 declaration is
  UniformContinuous.{0, 0} Rat Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))
but is expected to have type
  UniformContinuous.{0, 0} Rat Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instSupRat))
Case conversion may be inaccurate. Consider using '#align rat.uniform_continuous_abs Rat.uniformContinuous_absₓ'. -/
theorem uniformContinuous_abs : UniformContinuous (abs : ℚ → ℚ) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun a b h =>
      lt_of_le_of_lt (by simpa [Rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _) h⟩
#align rat.uniform_continuous_abs Rat.uniformContinuous_abs

/- warning: rat.continuous_mul -> Rat.continuous_mul is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} (Prod.{0, 0} Rat Rat) Rat (Prod.topologicalSpace.{0, 0} Rat Rat (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace))) (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)))) (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace))) (fun (p : Prod.{0, 0} Rat Rat) => HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) (Prod.fst.{0, 0} Rat Rat p) (Prod.snd.{0, 0} Rat Rat p))
but is expected to have type
  Continuous.{0, 0} (Prod.{0, 0} Rat Rat) Rat (instTopologicalSpaceProd.{0, 0} Rat Rat (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat))) (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)))) (UniformSpace.toTopologicalSpace.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat))) (fun (p : Prod.{0, 0} Rat Rat) => HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) (Prod.fst.{0, 0} Rat Rat p) (Prod.snd.{0, 0} Rat Rat p))
Case conversion may be inaccurate. Consider using '#align rat.continuous_mul Rat.continuous_mulₓ'. -/
theorem continuous_mul : Continuous fun p : ℚ × ℚ => p.1 * p.2 :=
  Rat.embedding_coe_real.continuous_iff.2 <| by
    simp [(· ∘ ·)] <;>
      exact real.continuous_mul.comp (rat.continuous_coe_real.prod_map Rat.continuous_coe_real)
#align rat.continuous_mul Rat.continuous_mul

instance : TopologicalRing ℚ :=
  { Rat.topologicalAddGroup with continuous_mul := Rat.continuous_mul }

/- warning: rat.totally_bounded_Icc -> Rat.totallyBounded_Icc is a dubious translation:
lean 3 declaration is
  forall (a : Rat) (b : Rat), TotallyBounded.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.metricSpace)) (Set.Icc.{0} Rat Rat.preorder a b)
but is expected to have type
  forall (a : Rat) (b : Rat), TotallyBounded.{0} Rat (PseudoMetricSpace.toUniformSpace.{0} Rat (MetricSpace.toPseudoMetricSpace.{0} Rat Rat.instMetricSpaceRat)) (Set.Icc.{0} Rat Rat.instPreorderRat a b)
Case conversion may be inaccurate. Consider using '#align rat.totally_bounded_Icc Rat.totallyBounded_Iccₓ'. -/
theorem totallyBounded_Icc (a b : ℚ) : TotallyBounded (Icc a b) := by
  simpa only [preimage_cast_Icc] using
    totallyBounded_preimage Rat.uniformEmbedding_coe_real (totallyBounded_Icc a b)
#align rat.totally_bounded_Icc Rat.totallyBounded_Icc

end Rat

