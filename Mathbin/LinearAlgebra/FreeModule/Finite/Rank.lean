/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module linear_algebra.free_module.finite.rank
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Finrank
import Mathbin.LinearAlgebra.FreeModule.Rank
import Mathbin.LinearAlgebra.FreeModule.Finite.Basic

/-!

# Rank of finite free modules

This is a basic API for the rank of finite free modules.

-/


--TODO: `linear_algebra/finite_dimensional` should import this file, and a lot of results should
--be moved here.
universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

open TensorProduct DirectSum BigOperators Cardinal

open Cardinal FiniteDimensional Fintype

namespace Module.Free

section Ring

variable [Ring R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

/-- The rank of a finite and free module is finite. -/
theorem rank_lt_aleph0 : Module.rank R M < ℵ₀ :=
  by
  letI := nontrivial_of_invariantBasisNumber R
  rw [← (choose_basis R M).mk_eq_dim'', lt_aleph_0_iff_fintype]
  exact Nonempty.intro inferInstance
#align module.free.rank_lt_aleph_0 Module.Free.rank_lt_aleph0

/-- If `M` is finite and free, `finrank M = rank M`. -/
@[simp]
theorem finrank_eq_rank : ↑(finrank R M) = Module.rank R M := by
  rw [finrank, cast_to_nat_of_lt_aleph_0 (rank_lt_aleph_0 R M)]
#align module.free.finrank_eq_rank Module.Free.finrank_eq_rank

/-- The finrank of a free module `M` over `R` is the cardinality of `choose_basis_index R M`. -/
theorem finrank_eq_card_chooseBasisIndex :
    finrank R M =
      @card (ChooseBasisIndex R M)
        (@ChooseBasisIndex.fintype R M _ _ _ _ (nontrivial_of_invariantBasisNumber R) _) :=
  by
  letI := nontrivial_of_invariantBasisNumber R
  simp [finrank, rank_eq_card_choose_basis_index]
#align module.free.finrank_eq_card_choose_basis_index Module.Free.finrank_eq_card_chooseBasisIndex

/-- The finrank of `(ι →₀ R)` is `fintype.card ι`. -/
@[simp]
theorem finrank_finsupp {ι : Type v} [Fintype ι] : finrank R (ι →₀ R) = card ι := by
  rw [finrank, rank_finsupp, ← mk_to_nat_eq_card, to_nat_lift]
#align module.free.finrank_finsupp Module.Free.finrank_finsupp

/-- The finrank of `(ι → R)` is `fintype.card ι`. -/
theorem finrank_pi {ι : Type v} [Fintype ι] : finrank R (ι → R) = card ι := by simp [finrank]
#align module.free.finrank_pi Module.Free.finrank_pi

/-- The finrank of the direct sum is the sum of the finranks. -/
@[simp]
theorem finrank_directSum {ι : Type v} [Fintype ι] (M : ι → Type w) [∀ i : ι, AddCommGroup (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (⨁ i, M i) = ∑ i, finrank R (M i) :=
  by
  letI := nontrivial_of_invariantBasisNumber R
  simp only [finrank, fun i => rank_eq_card_choose_basis_index R (M i), rank_direct_sum, ← mk_sigma,
    mk_to_nat_eq_card, card_sigma]
#align module.free.finrank_direct_sum Module.Free.finrank_directSum

/-- The finrank of `M × N` is `(finrank R M) + (finrank R N)`. -/
@[simp]
theorem finrank_prod : finrank R (M × N) = finrank R M + finrank R N := by
  simp [finrank, rank_lt_aleph_0 R M, rank_lt_aleph_0 R N]
#align module.free.finrank_prod Module.Free.finrank_prod

--TODO: this should follow from `linear_equiv.finrank_eq`, that is over a field.
/-- The finrank of a finite product is the sum of the finranks. -/
theorem finrank_pi_fintype {ι : Type v} [Fintype ι] {M : ι → Type w} [∀ i : ι, AddCommGroup (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (∀ i, M i) = ∑ i, finrank R (M i) :=
  by
  letI := nontrivial_of_invariantBasisNumber R
  simp only [finrank, fun i => rank_eq_card_choose_basis_index R (M i), rank_pi_finite, ← mk_sigma,
    mk_to_nat_eq_card, card_sigma]
#align module.free.finrank_pi_fintype Module.Free.finrank_pi_fintype

/-- If `m` and `n` are `fintype`, the finrank of `m × n` matrices is
  `(fintype.card m) * (fintype.card n)`. -/
theorem finrank_matrix (m n : Type v) [Fintype m] [Fintype n] :
    finrank R (Matrix m n R) = card m * card n := by simp [finrank]
#align module.free.finrank_matrix Module.Free.finrank_matrix

end Ring

section CommRing

variable [CommRing R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

/-- The finrank of `M ⊗[R] N` is `(finrank R M) * (finrank R N)`. -/
@[simp]
theorem finrank_tensorProduct (M : Type v) (N : Type w) [AddCommGroup M] [Module R M]
    [Module.Free R M] [AddCommGroup N] [Module R N] [Module.Free R N] :
    finrank R (M ⊗[R] N) = finrank R M * finrank R N := by simp [finrank]
#align module.free.finrank_tensor_product Module.Free.finrank_tensorProduct

end CommRing

end Module.Free

