import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Diagonal matrices

This file contains some results on the linear map corresponding to a
diagonal matrix (`range`, `ker` and `rank`).

## Tags

matrix, diagonal, linear_map
-/


noncomputable theory

open LinearMap Matrix Set Submodule

open_locale BigOperators

open_locale Matrix

universe u v w

namespace Matrix

section CommRingₓ

variable{n : Type _}[Fintype n][DecidableEq n]{R : Type v}[CommRingₓ R]

theorem proj_diagonal (i : n) (w : n → R) : (proj i).comp (to_lin' (diagonal w)) = w i • proj i :=
  by 
    ext j <;> simp [mul_vec_diagonal]

theorem diagonal_comp_std_basis (w : n → R) (i : n) :
  (diagonal w).toLin'.comp (LinearMap.stdBasis R (fun _ : n => R) i) = w i • LinearMap.stdBasis R (fun _ : n => R) i :=
  by 
    ext j 
    simpRw [LinearMap.comp_apply, to_lin'_apply, mul_vec_diagonal, LinearMap.smul_apply, Pi.smul_apply,
      Algebra.id.smul_eq_mul]
    byCases' i = j
    ·
      subst h
    ·
      rw [std_basis_ne R (fun _ : n => R) _ _ (Ne.symm h), _root_.mul_zero, _root_.mul_zero]

theorem diagonal_to_lin' (w : n → R) : (diagonal w).toLin' = LinearMap.pi fun i => w i • LinearMap.proj i :=
  by 
    ext v j <;> simp [mul_vec_diagonal]

end CommRingₓ

section Field

variable{m n : Type _}[Fintype m][Fintype n]

variable{K : Type u}[Field K]

-- error in LinearAlgebra.Matrix.Diagonal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ker_diagonal_to_lin'
[decidable_eq m]
(w : m → K) : «expr = »(ker (diagonal w).to_lin', «expr⨆ , »((i «expr ∈ » {i | «expr = »(w i, 0)}), range (linear_map.std_basis K (λ
    i, K) i))) :=
begin
  rw ["[", "<-", expr comap_bot, ",", "<-", expr infi_ker_proj, ",", expr comap_infi, "]"] [],
  have [] [] [":=", expr λ i : m, ker_comp (to_lin' (diagonal w)) (proj i)],
  simp [] [] ["only"] ["[", expr comap_infi, ",", "<-", expr this, ",", expr proj_diagonal, ",", expr ker_smul', "]"] [] [],
  have [] [":", expr «expr ⊆ »(univ, «expr ∪ »({i : m | «expr = »(w i, 0)}, «expr ᶜ»({i : m | «expr = »(w i, 0)})))] [],
  { rw [expr set.union_compl_self] [] },
  exact [expr (supr_range_std_basis_eq_infi_ker_proj K (λ
     i : m, K) disjoint_compl_right this (finite.of_fintype _)).symm]
end

theorem range_diagonal [DecidableEq m] (w : m → K) :
  (diagonal w).toLin'.range = ⨆(i : _)(_ : i ∈ { i | w i ≠ 0 }), (LinearMap.stdBasis K (fun i => K) i).range :=
  by 
    dsimp only [mem_set_of_eq]
    rw [←map_top, ←supr_range_std_basis, map_supr]
    congr 
    funext i 
    rw [←LinearMap.range_comp, diagonal_comp_std_basis, ←range_smul']

-- error in LinearAlgebra.Matrix.Diagonal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rank_diagonal
[decidable_eq m]
[decidable_eq K]
(w : m → K) : «expr = »(rank (diagonal w).to_lin', fintype.card {i // «expr ≠ »(w i, 0)}) :=
begin
  have [ident hu] [":", expr «expr ⊆ »(univ, «expr ∪ »(«expr ᶜ»({i : m | «expr = »(w i, 0)}), {i : m | «expr = »(w i, 0)}))] [],
  { rw [expr set.compl_union_self] [] },
  have [ident hd] [":", expr disjoint {i : m | «expr ≠ »(w i, 0)} {i : m | «expr = »(w i, 0)}] [":=", expr disjoint_compl_left],
  have [ident B₁] [] [":=", expr supr_range_std_basis_eq_infi_ker_proj K (λ i : m, K) hd hu (finite.of_fintype _)],
  have [ident B₂] [] [":=", expr @infi_ker_proj_equiv K _ _ (λ
    i : m, K) _ _ _ _ (by simp [] [] [] [] [] []; apply_instance) hd hu],
  rw ["[", expr rank, ",", expr range_diagonal, ",", expr B₁, ",", "<-", expr @dim_fun' K, "]"] [],
  apply [expr linear_equiv.dim_eq],
  apply [expr B₂]
end

end Field

end Matrix

