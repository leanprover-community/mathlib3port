/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module algebra.direct_sum.finsupp
! leanprover-community/mathlib commit aa3a420527e0fbfd0f6615b95b761254a9166e12
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.DirectSum.Module
import Mathbin.Data.Finsupp.ToDfinsupp

/-!
# Results on direct sums and finitely supported functions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

1. The linear equivalence between finitely supported functions `ι →₀ M` and
the direct sum of copies of `M` indexed by `ι`.
-/


universe u v w

noncomputable section

open DirectSum

open LinearMap Submodule

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

section finsuppLEquivDirectSum

variable (R M) (ι : Type _) [DecidableEq ι]

/-- The finitely supported functions `ι →₀ M` are in linear equivalence with the direct sum of
copies of M indexed by ι. -/
def finsuppLEquivDirectSum : (ι →₀ M) ≃ₗ[R] ⨁ i : ι, M :=
  haveI : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  finsuppLequivDfinsupp R
#align finsupp_lequiv_direct_sum finsuppLEquivDirectSum

@[simp]
theorem finsuppLEquivDirectSum_single (i : ι) (m : M) :
    finsuppLEquivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i m :=
  Finsupp.toDfinsupp_single i m
#align finsupp_lequiv_direct_sum_single finsuppLEquivDirectSum_single

@[simp]
theorem finsuppLEquivDirectSum_symm_lof (i : ι) (m : M) :
    (finsuppLEquivDirectSum R M ι).symm (DirectSum.lof R ι _ i m) = Finsupp.single i m :=
  letI : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  Dfinsupp.toFinsupp_single i m
#align finsupp_lequiv_direct_sum_symm_lof finsuppLEquivDirectSum_symm_lof

end finsuppLEquivDirectSum

