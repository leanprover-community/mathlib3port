/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Analysis.NormedSpace.ContinuousAffineMap
import Analysis.Calculus.ContDiff.Basic

#align_import analysis.calculus.affine_map from "leanprover-community/mathlib"@"fd4551cfe4b7484b81c2c9ba3405edae27659676"

/-!
# Smooth affine maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains results about smoothness of affine maps.

## Main definitions:

 * `continuous_affine_map.cont_diff`: a continuous affine map is smooth

-/


namespace ContinuousAffineMap

variable {𝕜 V W : Type _} [NontriviallyNormedField 𝕜]

variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]

variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]

#print ContinuousAffineMap.contDiff /-
/-- A continuous affine map between normed vector spaces is smooth. -/
theorem contDiff {n : ℕ∞} (f : V →A[𝕜] W) : ContDiff 𝕜 n f :=
  by
  rw [f.decomp]
  apply f.cont_linear.cont_diff.add
  simp only
  exact contDiff_const
#align continuous_affine_map.cont_diff ContinuousAffineMap.contDiff
-/

end ContinuousAffineMap

