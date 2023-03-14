/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module analysis.normed.group.completion
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Topology.Algebra.GroupCompletion
import Mathbin.Topology.MetricSpace.Completion

/-!
# Completion of a normed group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the completion of a (semi)normed group is a normed group.

## Tags

normed group, completion
-/


noncomputable section

namespace UniformSpace

namespace Completion

variable (E : Type _)

instance [UniformSpace E] [Norm E] : Norm (Completion E)
    where norm := Completion.extension Norm.norm

/- warning: uniform_space.completion.norm_coe -> UniformSpace.Completion.norm_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] (x : E), Eq.{1} Real (Norm.norm.{u1} (UniformSpace.Completion.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) (UniformSpace.Completion.hasNorm.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) (SeminormedAddCommGroup.toHasNorm.{u1} E _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) E (UniformSpace.Completion.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) (HasLiftT.mk.{succ u1, succ u1} E (UniformSpace.Completion.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) (CoeTCₓ.coe.{succ u1, succ u1} E (UniformSpace.Completion.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) (UniformSpace.Completion.hasCoeT.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))))) x)) (Norm.norm.{u1} E (SeminormedAddCommGroup.toHasNorm.{u1} E _inst_1) x)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] (x : E), Eq.{1} Real (Norm.norm.{u1} (UniformSpace.Completion.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) (UniformSpace.Completion.instNormCompletion.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) (SeminormedAddCommGroup.toNorm.{u1} E _inst_1)) (UniformSpace.Completion.coe'.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) x)) (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) x)
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.norm_coe UniformSpace.Completion.norm_coeₓ'. -/
@[simp]
theorem norm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ = ‖x‖ :=
  Completion.extension_coe uniformContinuous_norm x
#align uniform_space.completion.norm_coe UniformSpace.Completion.norm_coe

instance [SeminormedAddCommGroup E] : NormedAddCommGroup (Completion E) :=
  { Completion.addCommGroup, Completion.metricSpace with
    dist_eq := by
      intro x y
      apply completion.induction_on₂ x y <;> clear x y
      · refine' isClosed_eq (completion.uniform_continuous_extension₂ _).Continuous _
        exact Continuous.comp completion.continuous_extension continuous_sub
      · intro x y
        rw [← completion.coe_sub, norm_coe, completion.dist_eq, dist_eq_norm] }

end Completion

end UniformSpace

