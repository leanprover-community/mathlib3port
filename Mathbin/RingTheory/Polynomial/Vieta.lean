import Mathbin.RingTheory.Polynomial.Basic 
import Mathbin.RingTheory.Polynomial.Symmetric

/-!
# Vieta's Formula

The main result is `vieta.prod_X_add_C_eq_sum_esymm`, which shows that the product of linear terms
`λ + X i` is equal to a linear combination of the symmetric polynomials `esymm σ R j`.

## Implementation Notes:

We first take the viewpoint where the "roots" `X i` are variables. This means we work over
`polynomial (mv_polynomial σ R)`, which enables us to talk about linear combinations of
`esymm σ R j`. We then derive Vieta's formula in `polynomial R` by giving a
valuation from each `X i` to `r i`.

-/


universe u

open_locale BigOperators

open Finset Polynomial Fintype

namespace MvPolynomial

variable{R : Type u}[CommSemiringₓ R]

variable(σ : Type u)[Fintype σ]

-- error in RingTheory.Polynomial.Vieta: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A sum version of Vieta's formula. Viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
theorem prod_X_add_C_eq_sum_esymm : «expr = »((«expr∏ , »((i : σ), «expr + »(polynomial.C (X i), polynomial.X)) : polynomial (mv_polynomial σ R)), «expr∑ in , »((j), range «expr + »(card σ, 1), «expr * »(polynomial.C (esymm σ R j), «expr ^ »(polynomial.X, «expr - »(card σ, j))))) :=
begin
  classical,
  rw ["[", expr prod_add, ",", expr sum_powerset, "]"] [],
  refine [expr sum_congr (begin congr end) (λ j hj, _)],
  rw ["[", expr esymm, ",", expr polynomial.C.map_sum, ",", expr sum_mul, "]"] [],
  refine [expr sum_congr rfl (λ t ht, _)],
  have [ident h] [":", expr «expr = »(«expr \ »(univ, t).card, «expr - »(card σ, j))] [":=", expr by { rw [expr card_sdiff (mem_powerset_len.mp ht).1] [],
     congr,
     exact [expr (mem_powerset_len.mp ht).2] }],
  rw ["[", expr (polynomial.C : «expr →+* »(mv_polynomial σ R, polynomial _)).map_prod, ",", expr prod_const, ",", "<-", expr h, "]"] [],
  congr
end

-- error in RingTheory.Polynomial.Vieta: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A fully expanded sum version of Vieta's formula, evaluated at the roots.
The product of linear terms `X + r i` is equal to `∑ j in range (n + 1), e_j * X ^ (n - j)`,
where `e_j` is the `j`th symmetric polynomial of the constant terms `r i`. -/
theorem prod_X_add_C_eval
(r : σ → R) : «expr = »(«expr∏ , »((i : σ), «expr + »(polynomial.C (r i), polynomial.X)), «expr∑ in , »((i), range «expr + »(card σ, 1), «expr * »(«expr∑ in , »((t), powerset_len i (univ : finset σ), «expr∏ in , »((i), t, polynomial.C (r i))), «expr ^ »(polynomial.X, «expr - »(card σ, i))))) :=
begin
  classical,
  have [ident h] [] [":=", expr @prod_X_add_C_eq_sum_esymm _ _ σ _],
  apply_fun [expr polynomial.map (eval r)] ["at", ident h] [],
  rw ["[", expr map_prod, ",", expr map_sum, "]"] ["at", ident h],
  convert [] [expr h] [],
  simp [] [] ["only"] ["[", expr eval_X, ",", expr map_add, ",", expr polynomial.map_C, ",", expr polynomial.map_X, ",", expr eq_self_iff_true, "]"] [] [],
  funext [],
  simp [] [] ["only"] ["[", expr function.funext_iff, ",", expr esymm, ",", expr polynomial.map_C, ",", expr map_sum, ",", expr polynomial.C.map_sum, ",", expr polynomial.map_C, ",", expr map_pow, ",", expr polynomial.map_X, ",", expr map_mul, "]"] [] [],
  congr,
  funext [],
  simp [] [] ["only"] ["[", expr eval_prod, ",", expr eval_X, ",", expr (polynomial.C : «expr →+* »(R, polynomial R)).map_prod, "]"] [] []
end

theorem esymm_to_sum (r : σ → R) (j : ℕ) :
  Polynomial.c (eval r (esymm σ R j)) = ∑t in powerset_len j (univ : Finset σ), ∏i in t, Polynomial.c (r i) :=
  by 
    simp only [esymm, eval_sum, eval_prod, eval_X, polynomial.C.map_sum, (Polynomial.c : R →+* Polynomial _).map_prod]

-- error in RingTheory.Polynomial.Vieta: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Vieta's formula for the coefficients of the product of linear terms `X + r i`,
The `k`th coefficient is `∑ t in powerset_len (card σ - k) (univ : finset σ), ∏ i in t, r i`,
i.e. the symmetric polynomial `esymm σ R (card σ - k)` of the constant terms `r i`. -/
theorem prod_X_add_C_coeff
(r : σ → R)
(k : exprℕ())
(h : «expr ≤ »(k, card σ)) : «expr = »(polynomial.coeff «expr∏ , »((i : σ), «expr + »(polynomial.C (r i), polynomial.X)) k, «expr∑ in , »((t), powerset_len «expr - »(card σ, k) (univ : finset σ), «expr∏ in , »((i), t, r i))) :=
begin
  have [ident hk] [":", expr «expr = »(filter (λ
     x : exprℕ(), «expr = »(k, «expr - »(card σ, x))) (range «expr + »(card σ, 1)), {«expr - »(card σ, k)})] [":=", expr begin
     refine [expr finset.ext (λ a, ⟨λ ha, _, λ ha, _⟩)],
     rw [expr mem_singleton] [],
     have [ident hσ] [] [":=", expr (tsub_eq_iff_eq_add_of_le (mem_range_succ_iff.mp (mem_filter.mp ha).1)).mp (mem_filter.mp ha).2.symm],
     symmetry,
     rwa ["[", expr tsub_eq_iff_eq_add_of_le h, ",", expr add_comm, "]"] [],
     rw [expr mem_filter] [],
     have [ident haσ] [":", expr «expr ∈ »(a, range «expr + »(card σ, 1))] [":=", expr by { rw [expr mem_singleton.mp ha] [],
        exact [expr mem_range_succ_iff.mpr (@tsub_le_self _ _ _ _ _ k)] }],
     refine [expr ⟨haσ, eq.symm _⟩],
     rw [expr tsub_eq_iff_eq_add_of_le (mem_range_succ_iff.mp haσ)] [],
     have [ident hσ] [] [":=", expr (tsub_eq_iff_eq_add_of_le h).mp (mem_singleton.mp ha).symm],
     rwa [expr add_comm] []
   end],
  simp [] [] ["only"] ["[", expr prod_X_add_C_eval, ",", "<-", expr esymm_to_sum, ",", expr finset_sum_coeff, ",", expr coeff_C_mul_X, ",", expr sum_ite, ",", expr hk, ",", expr sum_singleton, ",", expr esymm, ",", expr eval_sum, ",", expr eval_prod, ",", expr eval_X, ",", expr add_zero, ",", expr sum_const_zero, "]"] [] []
end

end MvPolynomial

