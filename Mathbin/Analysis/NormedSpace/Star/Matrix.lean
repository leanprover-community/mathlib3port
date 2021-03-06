/-
Copyright (c) 2022 Hans Parshall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hans Parshall
-/
import Mathbin.Analysis.Matrix
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Data.Complex.IsROrC
import Mathbin.LinearAlgebra.UnitaryGroup

/-!
# Unitary matrices

This file collects facts about the unitary matrices over `ð` (either `â` or `â`).
-/


open BigOperators Matrix

variable {ð m n E : Type _}

section EntrywiseSupNorm

variable [IsROrC ð] [Fintype n] [DecidableEq n]

theorem entry_norm_bound_of_unitary {U : Matrix n n ð} (hU : U â Matrix.unitaryGroup n ð) (i j : n) : â¥U i jâ¥ â¤ 1 := by
  -- The norm squared of an entry is at most the L2 norm of its row.
  have norm_sum : â¥U i jâ¥ ^ 2 â¤ â x, â¥U i xâ¥ ^ 2 := by
    apply Multiset.single_le_sum
    Â· intro x h_x
      rw [Multiset.mem_map] at h_x
      cases' h_x with a h_a
      rw [â h_a.2]
      apply sq_nonneg
      
    Â· rw [Multiset.mem_map]
      use j
      simp only [â eq_self_iff_true, â Finset.mem_univ_val, â and_selfâ, â sq_eq_sq]
      
  -- The L2 norm of a row is a diagonal entry of U â¬ Uá´´
  have diag_eq_norm_sum : (U â¬ Uá´´) i i = â x : n, â¥U i xâ¥ ^ 2 := by
    simp only [â Matrix.mul_apply, â Matrix.conj_transpose_apply, star_ring_end_apply, â IsROrC.mul_conj, â
      IsROrC.norm_sq_eq_def', â IsROrC.of_real_pow]
  -- The L2 norm of a row is a diagonal entry of U â¬ Uá´´, real part
  have re_diag_eq_norm_sum : IsROrC.re ((U â¬ Uá´´) i i) = â x : n, â¥U i xâ¥ ^ 2 := by
    rw [IsROrC.ext_iff] at diag_eq_norm_sum
    rw [diag_eq_norm_sum.1]
    norm_cast
  -- Since U is unitary, the diagonal entries of U â¬ Uá´´ are all 1
  have mul_eq_one : U â¬ Uá´´ = 1 := unitary.mul_star_self_of_mem hU
  have diag_eq_one : IsROrC.re ((U â¬ Uá´´) i i) = 1 := by
    simp only [â mul_eq_one, â eq_self_iff_true, â Matrix.one_apply_eq, â IsROrC.one_re]
  -- Putting it all together
  rw [â sq_le_one_iff (norm_nonneg (U i j)), â diag_eq_one, re_diag_eq_norm_sum]
  exact norm_sum

attribute [local instance] Matrix.normedGroup

/-- The entrywise sup norm of a unitary matrix is at most 1. -/
theorem entrywise_sup_norm_bound_of_unitary {U : Matrix n n ð} (hU : U â Matrix.unitaryGroup n ð) : â¥Uâ¥ â¤ 1 := by
  simp_rw [pi_norm_le_iff zero_le_one]
  intro i j
  exact entry_norm_bound_of_unitary hU _ _

end EntrywiseSupNorm

