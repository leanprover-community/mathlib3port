/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Analysis.Normed.Group.Basic
import Topology.Algebra.GroupCompletion
import Topology.MetricSpace.Completion

#align_import analysis.normed.group.completion from "leanprover-community/mathlib"@"69c6a5a12d8a2b159f20933e60115a4f2de62b58"

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

#print UniformSpace.Completion.norm_coe /-
@[simp]
theorem norm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ = ‖x‖ :=
  Completion.extension_coe uniformContinuous_norm x
#align uniform_space.completion.norm_coe UniformSpace.Completion.norm_coe
-/

instance [SeminormedAddCommGroup E] : NormedAddCommGroup (Completion E) :=
  { Completion.addCommGroup, Completion.instMetricSpace with
    dist_eq := by
      intro x y
      apply completion.induction_on₂ x y <;> clear x y
      · refine' isClosed_eq (completion.uniform_continuous_extension₂ _).Continuous _
        exact Continuous.comp completion.continuous_extension continuous_sub
      · intro x y
        rw [← completion.coe_sub, norm_coe, completion.dist_eq, dist_eq_norm] }

end Completion

end UniformSpace

