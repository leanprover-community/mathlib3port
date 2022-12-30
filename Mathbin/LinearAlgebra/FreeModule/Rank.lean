/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module linear_algebra.free_module.rank
! leanprover-community/mathlib commit 986c4d5761f938b2e1c43c01f001b6d9d88c2055
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FreeModule.Basic
import Mathbin.LinearAlgebra.FinsuppVectorSpace

/-!

# Rank of free modules

This is a basic API for the rank of free modules.

-/


universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

open TensorProduct DirectSum BigOperators Cardinal

open Cardinal

namespace Module.Free

section Ring

variable [Ring R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

/-- The rank of a free module `M` over `R` is the cardinality of `choose_basis_index R M`. -/
theorem rank_eq_card_choose_basis_index : Module.rank R M = (#ChooseBasisIndex R M) :=
  (chooseBasis R M).mk_eq_dim''.symm
#align module.free.rank_eq_card_choose_basis_index Module.Free.rank_eq_card_choose_basis_index

/-- The rank of `(ι →₀ R)` is `(# ι).lift`. -/
@[simp]
theorem rank_finsupp {ι : Type v} : Module.rank R (ι →₀ R) = (#ι).lift := by
  simpa [lift_id', lift_umax] using (Basis.of_repr (LinearEquiv.refl _ (ι →₀ R))).mk_eq_dim.symm
#align module.free.rank_finsupp Module.Free.rank_finsupp

/-- If `R` and `ι` lie in the same universe, the rank of `(ι →₀ R)` is `# ι`. -/
theorem rank_finsupp' {ι : Type u} : Module.rank R (ι →₀ R) = (#ι) := by simp
#align module.free.rank_finsupp' Module.Free.rank_finsupp'

/-- The rank of `M × N` is `(module.rank R M).lift + (module.rank R N).lift`. -/
@[simp]
theorem rank_prod :
    Module.rank R (M × N) = lift.{w, v} (Module.rank R M) + lift.{v, w} (Module.rank R N) := by
  simpa [rank_eq_card_choose_basis_index R M, rank_eq_card_choose_basis_index R N, lift_umax,
    lift_umax'] using ((choose_basis R M).Prod (choose_basis R N)).mk_eq_dim.symm
#align module.free.rank_prod Module.Free.rank_prod

/-- If `M` and `N` lie in the same universe, the rank of `M × N` is
  `(module.rank R M) + (module.rank R N)`. -/
theorem rank_prod' (N : Type v) [AddCommGroup N] [Module R N] [Module.Free R N] :
    Module.rank R (M × N) = Module.rank R M + Module.rank R N := by simp
#align module.free.rank_prod' Module.Free.rank_prod'

/-- The rank of the direct sum is the sum of the ranks. -/
@[simp]
theorem rank_direct_sum {ι : Type v} (M : ι → Type w) [∀ i : ι, AddCommGroup (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] :
    Module.rank R (⨁ i, M i) = Cardinal.sum fun i => Module.rank R (M i) :=
  by
  let B i := choose_basis R (M i)
  let b : Basis _ R (⨁ i, M i) := Dfinsupp.basis fun i => B i
  simp [← b.mk_eq_dim'', fun i => (B i).mk_eq_dim'']
#align module.free.rank_direct_sum Module.Free.rank_direct_sum

/-- The rank of a finite product is the sum of the ranks. -/
@[simp]
theorem rank_pi_finite {ι : Type v} [Finite ι] {M : ι → Type w} [∀ i : ι, AddCommGroup (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] :
    Module.rank R (∀ i, M i) = Cardinal.sum fun i => Module.rank R (M i) :=
  by
  cases nonempty_fintype ι
  rw [← (DirectSum.linearEquivFunOnFintype _ _ M).dim_eq, rank_direct_sum]
#align module.free.rank_pi_finite Module.Free.rank_pi_finite

/-- If `m` and `n` are `fintype`, the rank of `m × n` matrices is `(# m).lift * (# n).lift`. -/
@[simp]
theorem rank_matrix (m : Type v) (n : Type w) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = lift.{max v w u, v} (#m) * lift.{max v w u, w} (#n) :=
  by
  cases nonempty_fintype m
  cases nonempty_fintype n
  have h := (Matrix.stdBasis R m n).mk_eq_dim
  rw [← lift_lift.{max v w u, max v w}, lift_inj] at h
  simpa using h.symm
#align module.free.rank_matrix Module.Free.rank_matrix

/-- If `m` and `n` are `fintype` that lie in the same universe, the rank of `m × n` matrices is
  `(# n * # m).lift`. -/
@[simp]
theorem rank_matrix' (m n : Type v) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = ((#m) * (#n)).lift := by rw [rank_matrix, lift_mul, lift_umax]
#align module.free.rank_matrix' Module.Free.rank_matrix'

/-- If `m` and `n` are `fintype` that lie in the same universe as `R`, the rank of `m × n` matrices
  is `# m * # n`. -/
@[simp]
theorem rank_matrix'' (m n : Type u) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = (#m) * (#n) := by simp
#align module.free.rank_matrix'' Module.Free.rank_matrix''

end Ring

section CommRing

variable [CommRing R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

/-- The rank of `M ⊗[R] N` is `(module.rank R M).lift * (module.rank R N).lift`. -/
@[simp]
theorem rank_tensor_product :
    Module.rank R (M ⊗[R] N) = lift.{w, v} (Module.rank R M) * lift.{v, w} (Module.rank R N) :=
  by
  let ιM := choose_basis_index R M
  let ιN := choose_basis_index R N
  have h₁ := LinearEquiv.lift_dim_eq (TensorProduct.congr (repr R M) (repr R N))
  let b : Basis (ιM × ιN) R (_ →₀ R) := Finsupp.basisSingleOne
  rw [LinearEquiv.dim_eq (finsuppTensorFinsupp' R ιM ιN), ← b.mk_eq_dim, mk_prod] at h₁
  rw [lift_inj.1 h₁, rank_eq_card_choose_basis_index R M, rank_eq_card_choose_basis_index R N]
#align module.free.rank_tensor_product Module.Free.rank_tensor_product

/-- If `M` and `N` lie in the same universe, the rank of `M ⊗[R] N` is
  `(module.rank R M) * (module.rank R N)`. -/
theorem rank_tensor_product' (N : Type v) [AddCommGroup N] [Module R N] [Module.Free R N] :
    Module.rank R (M ⊗[R] N) = Module.rank R M * Module.rank R N := by simp
#align module.free.rank_tensor_product' Module.Free.rank_tensor_product'

end CommRing

end Module.Free

