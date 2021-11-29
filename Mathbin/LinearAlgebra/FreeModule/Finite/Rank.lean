import Mathbin.LinearAlgebra.FreeModule.Rank 
import Mathbin.LinearAlgebra.FreeModule.Finite.Basic

/-!

# Rank of finite free modules

This is a basic API for the rank of finite free modules.

-/


universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

open_locale TensorProduct DirectSum BigOperators Cardinal

open Cardinal FiniteDimensional Fintype

namespace Module.Free

section Ringₓ

variable [Ringₓ R] [StrongRankCondition R]

variable [AddCommGroupₓ M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroupₓ N] [Module R N] [Module.Free R N] [Module.Finite R N]

-- error in LinearAlgebra.FreeModule.Finite.Rank: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The rank of a finite and free module is finite. -/ theorem rank_lt_omega : «expr < »(module.rank R M, exprω()) :=
begin
  letI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  rw ["[", "<-", expr (choose_basis R M).mk_eq_dim'', ",", expr lt_omega_iff_fintype, "]"] [],
  exact [expr nonempty.intro infer_instance]
end

/-- If `M` is finite and free, `finrank M = rank M`. -/
@[simp]
theorem finrank_eq_rank : «expr↑ » (finrank R M) = Module.rank R M :=
  by 
    rw [finrank, cast_to_nat_of_lt_omega (rank_lt_omega R M)]

-- error in LinearAlgebra.FreeModule.Finite.Rank: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The finrank of a free module `M` over `R` is the cardinality of `choose_basis_index R M`. -/
theorem finrank_eq_card_choose_basis_index : «expr = »(finrank R M, @card (choose_basis_index R M) (@choose_basis_index.fintype R M _ _ _ _ (nontrivial_of_invariant_basis_number R) _)) :=
begin
  letI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  simp [] [] [] ["[", expr finrank, ",", expr rank_eq_card_choose_basis_index, "]"] [] []
end

/-- The finrank of `(ι →₀ R)` is `fintype.card ι`. -/
@[simp]
theorem finrank_finsupp {ι : Type v} [Fintype ι] : finrank R (ι →₀ R) = card ι :=
  by 
    rw [finrank, rank_finsupp, ←mk_to_nat_eq_card, to_nat_lift]

/-- The finrank of `(ι → R)` is `fintype.card ι`. -/
theorem finrank_pi {ι : Type v} [Fintype ι] : finrank R (ι → R) = card ι :=
  by 
    simp [finrank]

-- error in LinearAlgebra.FreeModule.Finite.Rank: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The finrank of the direct sum is the sum of the finranks. -/
@[simp]
theorem finrank_direct_sum
{ι : Type v}
[fintype ι]
(M : ι → Type w)
[∀ i : ι, add_comm_group (M i)]
[∀ i : ι, module R (M i)]
[∀ i : ι, module.free R (M i)]
[∀ i : ι, module.finite R (M i)] : «expr = »(finrank R «expr⨁ , »((i), M i), «expr∑ , »((i), finrank R (M i))) :=
begin
  letI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  simp [] [] ["only"] ["[", expr finrank, ",", expr λ
   i, rank_eq_card_choose_basis_index R (M i), ",", expr rank_direct_sum, ",", "<-", expr mk_sigma, ",", expr mk_to_nat_eq_card, ",", expr card_sigma, "]"] [] []
end

/-- The finrank of `M × N` is `(finrank R M) + (finrank R N)`. -/
@[simp]
theorem finrank_prod : finrank R (M × N) = finrank R M+finrank R N :=
  by 
    simp [finrank, rank_lt_omega R M, rank_lt_omega R N]

-- error in LinearAlgebra.FreeModule.Finite.Rank: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The finrank of a finite product is the sum of the finranks. -/
theorem finrank_pi_fintype
{ι : Type v}
[fintype ι]
{M : ι → Type w}
[∀ i : ι, add_comm_group (M i)]
[∀ i : ι, module R (M i)]
[∀ i : ι, module.free R (M i)]
[∀ i : ι, module.finite R (M i)] : «expr = »(finrank R (∀ i, M i), «expr∑ , »((i), finrank R (M i))) :=
begin
  letI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  simp [] [] ["only"] ["[", expr finrank, ",", expr λ
   i, rank_eq_card_choose_basis_index R (M i), ",", expr rank_pi_fintype, ",", "<-", expr mk_sigma, ",", expr mk_to_nat_eq_card, ",", expr card_sigma, "]"] [] []
end

/-- If `n` and `m` are `fintype`, the finrank of `n × m` matrices is
  `(fintype.card n) * (fintype.card m)`. -/
theorem finrank_matrix (n : Type v) [Fintype n] (m : Type w) [Fintype m] : finrank R (Matrix n m R) = card n*card m :=
  by 
    simp [finrank]

end Ringₓ

section CommRingₓ

variable [CommRingₓ R] [StrongRankCondition R]

variable [AddCommGroupₓ M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroupₓ N] [Module R N] [Module.Free R N] [Module.Finite R N]

-- error in LinearAlgebra.FreeModule.Finite.Rank: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The finrank of `M →ₗ[R] N` is `(finrank R M) * (finrank R N)`. -/
theorem finrank_linear_hom : «expr = »(finrank R «expr →ₗ[ ] »(M, R, N), «expr * »(finrank R M, finrank R N)) :=
begin
  classical,
  letI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  have [ident h] [] [":=", expr linear_map.to_matrix (choose_basis R M) (choose_basis R N)],
  let [ident b] [] [":=", expr (matrix.std_basis _ _ _).map h.symm],
  rw ["[", expr finrank, ",", expr dim_eq_card_basis b, ",", "<-", expr mk_fintype, ",", expr mk_to_nat_eq_card, ",", expr finrank, ",", expr finrank, ",", expr rank_eq_card_choose_basis_index, ",", expr rank_eq_card_choose_basis_index, ",", expr mk_to_nat_eq_card, ",", expr mk_to_nat_eq_card, ",", expr card_prod, ",", expr mul_comm, "]"] []
end

/-- The finrank of `M ⊗[R] N` is `(finrank R M) * (finrank R N)`. -/
@[simp]
theorem finrank_tensor_product (M : Type v) (N : Type w) [AddCommGroupₓ M] [Module R M] [Module.Free R M]
  [AddCommGroupₓ N] [Module R N] [Module.Free R N] : finrank R (M ⊗[R] N) = finrank R M*finrank R N :=
  by 
    simp [finrank]

end CommRingₓ

end Module.Free

