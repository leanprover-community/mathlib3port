/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module linear_algebra.free_module.rank
! leanprover-community/mathlib commit 4f4a1c875d0baa92ab5d92f3fb1bb258ad9f3e5b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Dimension

/-!

# Extra results about `module.rank`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some extra results not in `linear_algebra.dimension`.

-/


universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

open scoped TensorProduct DirectSum BigOperators Cardinal

open Cardinal

section Ring

variable [Ring R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

open Module.Free

#print rank_finsupp /-
@[simp]
theorem rank_finsupp (ι : Type w) :
    Module.rank R (ι →₀ M) = Cardinal.lift.{v} (#ι) * Cardinal.lift.{w} (Module.rank R M) :=
  by
  obtain ⟨⟨_, bs⟩⟩ := Module.Free.exists_basis R M
  rw [← bs.mk_eq_rank'', ← (Finsupp.basis fun a : ι => bs).mk_eq_rank'', Cardinal.mk_sigma,
    Cardinal.sum_const]
#align rank_finsupp rank_finsupp
-/

#print rank_finsupp' /-
theorem rank_finsupp' (ι : Type v) : Module.rank R (ι →₀ M) = (#ι) * Module.rank R M := by
  simp [rank_finsupp]
#align rank_finsupp' rank_finsupp'
-/

#print rank_finsupp_self /-
/-- The rank of `(ι →₀ R)` is `(# ι).lift`. -/
@[simp]
theorem rank_finsupp_self (ι : Type w) : Module.rank R (ι →₀ R) = (#ι).lift := by
  simp [rank_finsupp]
#align rank_finsupp_self rank_finsupp_self
-/

#print rank_finsupp_self' /-
/-- If `R` and `ι` lie in the same universe, the rank of `(ι →₀ R)` is `# ι`. -/
theorem rank_finsupp_self' {ι : Type u} : Module.rank R (ι →₀ R) = (#ι) := by simp
#align rank_finsupp_self' rank_finsupp_self'
-/

#print rank_directSum /-
/-- The rank of the direct sum is the sum of the ranks. -/
@[simp]
theorem rank_directSum {ι : Type v} (M : ι → Type w) [∀ i : ι, AddCommGroup (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] :
    Module.rank R (⨁ i, M i) = Cardinal.sum fun i => Module.rank R (M i) :=
  by
  let B i := choose_basis R (M i)
  let b : Basis _ R (⨁ i, M i) := Dfinsupp.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']
#align rank_direct_sum rank_directSum
-/

#print rank_matrix /-
/-- If `m` and `n` are `fintype`, the rank of `m × n` matrices is `(# m).lift * (# n).lift`. -/
@[simp]
theorem rank_matrix (m : Type v) (n : Type w) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = lift.{max v w u, v} (#m) * lift.{max v w u, w} (#n) :=
  by
  cases nonempty_fintype m
  cases nonempty_fintype n
  have h := (Matrix.stdBasis R m n).mk_eq_rank
  rw [← lift_lift.{max v w u, max v w}, lift_inj] at h 
  simpa using h.symm
#align rank_matrix rank_matrix
-/

#print rank_matrix' /-
/-- If `m` and `n` are `fintype` that lie in the same universe, the rank of `m × n` matrices is
  `(# n * # m).lift`. -/
@[simp]
theorem rank_matrix' (m n : Type v) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = ((#m) * (#n)).lift := by rw [rank_matrix, lift_mul, lift_umax]
#align rank_matrix' rank_matrix'
-/

#print rank_matrix'' /-
/-- If `m` and `n` are `fintype` that lie in the same universe as `R`, the rank of `m × n` matrices
  is `# m * # n`. -/
@[simp]
theorem rank_matrix'' (m n : Type u) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = (#m) * (#n) := by simp
#align rank_matrix'' rank_matrix''
-/

end Ring

section CommRing

variable [CommRing R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

open Module.Free

#print rank_tensorProduct /-
/-- The rank of `M ⊗[R] N` is `(module.rank R M).lift * (module.rank R N).lift`. -/
@[simp]
theorem rank_tensorProduct :
    Module.rank R (M ⊗[R] N) = lift.{w, v} (Module.rank R M) * lift.{v, w} (Module.rank R N) :=
  by
  obtain ⟨⟨_, bM⟩⟩ := Module.Free.exists_basis R M
  obtain ⟨⟨_, bN⟩⟩ := Module.Free.exists_basis R N
  rw [← bM.mk_eq_rank'', ← bN.mk_eq_rank'', ← (bM.tensor_product bN).mk_eq_rank'', Cardinal.mk_prod]
#align rank_tensor_product rank_tensorProduct
-/

#print rank_tensorProduct' /-
/-- If `M` and `N` lie in the same universe, the rank of `M ⊗[R] N` is
  `(module.rank R M) * (module.rank R N)`. -/
theorem rank_tensorProduct' (N : Type v) [AddCommGroup N] [Module R N] [Module.Free R N] :
    Module.rank R (M ⊗[R] N) = Module.rank R M * Module.rank R N := by simp
#align rank_tensor_product' rank_tensorProduct'
-/

end CommRing

