import Mathbin.LinearAlgebra.FreeModule.Basic 
import Mathbin.LinearAlgebra.FinsuppVectorSpace

/-!

# Rank of free modules

This is a basic API for the rank of free modules.

-/


universe u v w

variable(R : Type u)(M : Type v)(N : Type w)

open_locale TensorProduct DirectSum BigOperators Cardinal

open Cardinal

namespace Module.Free

section Ringₓ

variable[Ringₓ R][StrongRankCondition R]

variable[AddCommGroupₓ M][Module R M][Module.Free R M]

variable[AddCommGroupₓ N][Module R N][Module.Free R N]

/-- The rank of a free module `M` over `R` is the cardinality of `choose_basis_index R M`. -/
theorem rank_eq_card_choose_basis_index : Module.rank R M = # (choose_basis_index R M) :=
  (choose_basis R M).mk_eq_dim''.symm

/-- The rank of `(ι →₀ R)` is `(# ι).lift`. -/
@[simp]
theorem rank_finsupp {ι : Type v} : Module.rank R (ι →₀ R) = (# ι).lift :=
  by 
    simpa [lift_id', lift_umax] using (Basis.of_repr (LinearEquiv.refl _ (ι →₀ R))).mk_eq_dim.symm

/-- If `R` and `ι` lie in the same universe, the rank of `(ι →₀ R)` is `# ι`. -/
theorem rank_finsupp' {ι : Type u} : Module.rank R (ι →₀ R) = # ι :=
  by 
    simp 

/-- The rank of `M × N` is `(module.rank R M).lift + (module.rank R N).lift`. -/
@[simp]
theorem rank_prod : Module.rank R (M × N) = lift.{w, v} (Module.rank R M)+lift.{v, w} (Module.rank R N) :=
  by 
    simpa [rank_eq_card_choose_basis_index R M, rank_eq_card_choose_basis_index R N, lift_umax, lift_umax'] using
      ((choose_basis R M).Prod (choose_basis R N)).mk_eq_dim.symm

/-- If `M` and `N` lie in the same universe, the rank of `M × N` is
  `(module.rank R M) + (module.rank R N)`. -/
theorem rank_prod' (N : Type v) [AddCommGroupₓ N] [Module R N] [Module.Free R N] :
  Module.rank R (M × N) = Module.rank R M+Module.rank R N :=
  by 
    simp 

/-- The rank of the direct sum is the sum of the ranks. -/
@[simp]
theorem rank_direct_sum {ι : Type v} (M : ι → Type w) [∀ i : ι, AddCommGroupₓ (M i)] [∀ i : ι, Module R (M i)]
  [∀ i : ι, Module.Free R (M i)] : Module.rank R (⨁i, M i) = Cardinal.sum fun i => Module.rank R (M i) :=
  by 
    let B := fun i => choose_basis R (M i)
    let b : Basis _ R (⨁i, M i) := Dfinsupp.basis fun i => B i 
    simp [←b.mk_eq_dim'', fun i => (B i).mk_eq_dim'']

/-- The rank of a finite product is the sum of the ranks. -/
@[simp]
theorem rank_pi_fintype {ι : Type v} [Fintype ι] {M : ι → Type w} [∀ i : ι, AddCommGroupₓ (M i)]
  [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] :
  Module.rank R (∀ i, M i) = Cardinal.sum fun i => Module.rank R (M i) :=
  by 
    rw [←(DirectSum.linearEquivFunOnFintype _ _ M).dim_eq, rank_direct_sum]

-- error in LinearAlgebra.FreeModule.Rank: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `n` and `m` are `fintype`, the rank of `n × m` matrices is `(# n).lift * (# m).lift`. -/
@[simp]
theorem rank_matrix
(n : Type v)
[fintype n]
(m : Type w)
[fintype m] : «expr = »(module.rank R (matrix n m R), «expr * »(lift.{max v w u, v} («expr#»() n), lift.{max v w u, w} («expr#»() m))) :=
begin
  have [ident h] [] [":=", expr (matrix.std_basis R n m).mk_eq_dim],
  rw ["[", "<-", expr lift_lift.{max v w u, max v w}, ",", expr lift_inj, "]"] ["at", ident h],
  simpa [] [] [] [] [] ["using", expr h.symm]
end

/-- If `n` and `m` are `fintype` that lie in the same universe, the rank of `n × m` matrices is
  `(# n * # m).lift`. -/
@[simp]
theorem rank_matrix' (n : Type v) [Fintype n] (m : Type v) [Fintype m] :
  Module.rank R (Matrix n m R) = (# n*# m).lift :=
  by 
    rw [rank_matrix, lift_mul, lift_umax]

/-- If `n` and `m` are `fintype` that lie in the same universe as `R`, the rank of `n × m` matrices
  is `# n * # m`. -/
@[simp]
theorem rank_matrix'' (n : Type u) [Fintype n] (m : Type u) [Fintype m] : Module.rank R (Matrix n m R) = # n*# m :=
  by 
    simp 

end Ringₓ

section CommRingₓ

variable[CommRingₓ R][StrongRankCondition R]

variable[AddCommGroupₓ M][Module R M][Module.Free R M]

variable[AddCommGroupₓ N][Module R N][Module.Free R N]

-- error in LinearAlgebra.FreeModule.Rank: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The rank of `M ⊗[R] N` is `(module.rank R M).lift * (module.rank R N).lift`. -/
@[simp]
theorem rank_tensor_product : «expr = »(module.rank R «expr ⊗[ ] »(M, R, N), «expr * »(lift.{w, v} (module.rank R M), lift.{v, w} (module.rank R N))) :=
begin
  let [ident ιM] [] [":=", expr choose_basis_index R M],
  let [ident ιN] [] [":=", expr choose_basis_index R N],
  have [ident h₁] [] [":=", expr linear_equiv.lift_dim_eq (tensor_product.congr (repr R M) (repr R N))],
  let [ident b] [":", expr basis «expr × »(ιM, ιN) R «expr →₀ »(_, R)] [":=", expr finsupp.basis_single_one],
  rw ["[", expr linear_equiv.dim_eq (finsupp_tensor_finsupp' R ιM ιN), ",", "<-", expr b.mk_eq_dim, ",", expr mk_prod, "]"] ["at", ident h₁],
  rw ["[", expr lift_inj.1 h₁, ",", expr rank_eq_card_choose_basis_index R M, ",", expr rank_eq_card_choose_basis_index R N, "]"] []
end

/-- If `M` and `N` lie in the same universe, the rank of `M ⊗[R] N` is
  `(module.rank R M) * (module.rank R N)`. -/
theorem rank_tensor_product' (N : Type v) [AddCommGroupₓ N] [Module R N] [Module.Free R N] :
  Module.rank R (M ⊗[R] N) = Module.rank R M*Module.rank R N :=
  by 
    simp 

end CommRingₓ

end Module.Free

