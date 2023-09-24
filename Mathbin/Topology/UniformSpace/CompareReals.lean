/-
Copyright (c) 2019 Patrick MAssot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Topology.UniformSpace.AbsoluteValue
import Topology.Instances.Real
import Topology.Instances.Rat
import Topology.UniformSpace.Completion

#align_import topology.uniform_space.compare_reals from "leanprover-community/mathlib"@"69c6a5a12d8a2b159f20933e60115a4f2de62b58"

/-!
# Comparison of Cauchy reals and Bourbaki reals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In `data.real.basic` real numbers are defined using the so called Cauchy construction (although
it is due to Georg Cantor). More precisely, this construction applies to commutative rings equipped
with an absolute value with values in a linear ordered field.

On the other hand, in the `uniform_space` folder, we construct completions of general uniform
spaces, which allows to construct the Bourbaki real numbers. In this file we build uniformly
continuous bijections from Cauchy reals to Bourbaki reals and back. This is a cross sanity check of
both constructions. Of course those two constructions are variations on the completion idea, simply
with different level of generality. Comparing with Dedekind cuts or quasi-morphisms would be of a
completely different nature.

Note that `metric_space/cau_seq_filter` also relates the notions of Cauchy sequences in metric
spaces and Cauchy filters in general uniform spaces, and `metric_space/completion` makes sure
the completion (as a uniform space) of a metric space is a metric space.

Historical note: mathlib used to define real numbers in an intermediate way, using completion
of uniform spaces but extending multiplication in an ad-hoc way.

TODO:
* Upgrade this isomorphism to a topological ring isomorphism.
* Do the same comparison for p-adic numbers

## Implementation notes

The heavy work is done in `topology/uniform_space/abstract_completion` which provides an abstract
caracterization of completions of uniform spaces, and isomorphisms between them. The only work left
here is to prove the uniform space structure coming from the absolute value on ℚ (with values in ℚ,
not referring to ℝ) coincides with the one coming from the metric space structure (which of course
does use ℝ).

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

real numbers, completion, uniform spaces
-/


open Set Function Filter CauSeq UniformSpace

#print Rat.uniformSpace_eq /-
/-- The metric space uniform structure on ℚ (which presupposes the existence
of real numbers) agrees with the one coming directly from (abs : ℚ → ℚ). -/
theorem Rat.uniformSpace_eq :
    (AbsoluteValue.abs : AbsoluteValue ℚ ℚ).UniformSpace = PseudoMetricSpace.toUniformSpace :=
  by
  ext s
  rw [(AbsoluteValue.hasBasis_uniformity _).mem_iff, metric.uniformity_basis_dist_rat.mem_iff]
  simp only [Rat.dist_eq, AbsoluteValue.abs_apply, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_lt,
    abs_sub_comm]
#align rat.uniform_space_eq Rat.uniformSpace_eq
-/

#print rationalCauSeqPkg /-
/-- Cauchy reals packaged as a completion of ℚ using the absolute value route. -/
def rationalCauSeqPkg : @AbstractCompletion ℚ <| (@AbsoluteValue.abs ℚ _).UniformSpace
    where
  Space := ℝ
  coe := (coe : ℚ → ℝ)
  uniformStruct := by infer_instance
  complete := by infer_instance
  separation := by infer_instance
  UniformInducing := by
    rw [Rat.uniformSpace_eq]
    exact rat.uniform_embedding_coe_real.to_uniform_inducing
  dense := Rat.denseEmbedding_coe_real.dense
#align rational_cau_seq_pkg rationalCauSeqPkg
-/

namespace CompareReals

#print CompareReals.Q /-
/-- Type wrapper around ℚ to make sure the absolute value uniform space instance is picked up
instead of the metric space one. We proved in rat.uniform_space_eq that they are equal,
but they are not definitionaly equal, so it would confuse the type class system (and probably
also human readers). -/
def Q :=
  ℚ
deriving CommRing, Inhabited
#align compare_reals.Q CompareReals.Q
-/

instance : UniformSpace Q :=
  (@AbsoluteValue.abs ℚ _).UniformSpace

#print CompareReals.Bourbakiℝ /-
/-- Real numbers constructed as in Bourbaki. -/
def Bourbakiℝ : Type :=
  Completion Q
deriving Inhabited
#align compare_reals.Bourbakiℝ CompareReals.Bourbakiℝ
-/

#print CompareReals.Bourbaki.uniformSpace /-
instance Bourbaki.uniformSpace : UniformSpace Bourbakiℝ :=
  Completion.uniformSpace Q
#align compare_reals.bourbaki.uniform_space CompareReals.Bourbaki.uniformSpace
-/

#print CompareReals.bourbakiPkg /-
/-- Bourbaki reals packaged as a completion of Q using the general theory. -/
def bourbakiPkg : AbstractCompletion Q :=
  Completion.cPkg
#align compare_reals.Bourbaki_pkg CompareReals.bourbakiPkg
-/

#print CompareReals.compareEquiv /-
/-- The uniform bijection between Bourbaki and Cauchy reals. -/
noncomputable def compareEquiv : Bourbakiℝ ≃ᵤ ℝ :=
  bourbakiPkg.compareEquiv rationalCauSeqPkg
#align compare_reals.compare_equiv CompareReals.compareEquiv
-/

#print CompareReals.compare_uc /-
theorem compare_uc : UniformContinuous compareEquiv :=
  bourbakiPkg.uniformContinuous_compareEquiv _
#align compare_reals.compare_uc CompareReals.compare_uc
-/

#print CompareReals.compare_uc_symm /-
theorem compare_uc_symm : UniformContinuous compareEquiv.symm :=
  bourbakiPkg.uniformContinuous_compareEquiv_symm _
#align compare_reals.compare_uc_symm CompareReals.compare_uc_symm
-/

end CompareReals

