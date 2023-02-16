/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module analysis.normed_space.dual_number
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.DualNumber
import Mathbin.Analysis.NormedSpace.TrivSqZeroExt

/-!
# Results on `dual_number R` related to the norm

These are just restatements of similar statements about `triv_sq_zero_ext R M`.

## Main results

* `exp_eps`

-/


namespace DualNumber

open TrivSqZeroExt

variable (𝕜 : Type _) {R : Type _}

variable [IsROrC 𝕜] [NormedCommRing R] [NormedAlgebra 𝕜 R]

variable [TopologicalRing R] [CompleteSpace R] [T2Space R]

@[simp]
theorem exp_eps : exp 𝕜 (eps : DualNumber R) = 1 + eps :=
  exp_inr _ _
#align dual_number.exp_eps DualNumber.exp_eps

@[simp]
theorem exp_smul_eps (r : R) : exp 𝕜 (r • eps : DualNumber R) = 1 + r • eps := by
  rw [eps, ← inr_smul, exp_inr]
#align dual_number.exp_smul_eps DualNumber.exp_smul_eps

end DualNumber

