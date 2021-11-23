import Mathbin.Algebra.Polynomial.BigOperators 
import Mathbin.Data.Matrix.CharP 
import Mathbin.FieldTheory.Finite.Basic 
import Mathbin.GroupTheory.Perm.Cycles 
import Mathbin.LinearAlgebra.Matrix.Charpoly.Basic 
import Mathbin.LinearAlgebra.Matrix.Trace 
import Mathbin.LinearAlgebra.Matrix.ToLin 
import Mathbin.RingTheory.Polynomial.Basic 
import Mathbin.RingTheory.PowerBasis

/-!
# Characteristic polynomials

We give methods for computing coefficients of the characteristic polynomial.

## Main definitions

- `matrix.charpoly_degree_eq_dim` proves that the degree of the characteristic polynomial
  over a nonzero ring is the dimension of the matrix
- `matrix.det_eq_sign_charpoly_coeff` proves that the determinant is the constant term of the
  characteristic polynomial, up to sign.
- `matrix.trace_eq_neg_charpoly_coeff` proves that the trace is the negative of the (d-1)th
  coefficient of the characteristic polynomial, where d is the dimension of the matrix.
  For a nonzero ring, this is the second-highest coefficient.

-/


noncomputable theory

universe u v w z

open Polynomial Matrix

open_locale BigOperators

variable{R : Type u}[CommRingₓ R]

variable{n G : Type v}[DecidableEq n][Fintype n]

variable{α β : Type v}[DecidableEq α]

open Finset

variable{M : Matrix n n R}

theorem charmatrix_apply_nat_degree [Nontrivial R] (i j : n) : (charmatrix M i j).natDegree = ite (i = j) 1 0 :=
  by 
    byCases' i = j <;> simp [h, ←degree_eq_iff_nat_degree_eq_of_pos (Nat.succ_posₓ 0)]

theorem charmatrix_apply_nat_degree_le (i j : n) : (charmatrix M i j).natDegree ≤ ite (i = j) 1 0 :=
  by 
    splitIfs <;> simp [h, nat_degree_X_sub_C_le]

namespace Matrix

variable(M)

theorem charpoly_sub_diagonal_degree_lt : (M.charpoly - ∏i : n, X - C (M i i)).degree < «expr↑ » (Fintype.card n - 1) :=
  by 
    rw [charpoly, det_apply', ←insert_erase (mem_univ (Equiv.refl n)), sum_insert (not_mem_erase (Equiv.refl n) univ),
      add_commₓ]
    simp only [charmatrix_apply_eq, one_mulₓ, Equiv.Perm.sign_refl, id.def, Int.cast_one, Units.coe_one, add_sub_cancel,
      Equiv.coe_refl]
    rw [←mem_degree_lt]
    apply Submodule.sum_mem (degree_lt R (Fintype.card n - 1))
    intro c hc 
    rw [←C_eq_int_cast, C_mul']
    apply Submodule.smul_mem (degree_lt R (Fintype.card n - 1)) («expr↑ » («expr↑ » (Equiv.Perm.sign c)))
    rw [mem_degree_lt]
    apply lt_of_le_of_ltₓ degree_le_nat_degree _ 
    rw [WithBot.coe_lt_coe]
    apply lt_of_le_of_ltₓ _ (Equiv.Perm.fixed_point_card_lt_of_ne_one (ne_of_mem_erase hc))
    apply le_transₓ (Polynomial.nat_degree_prod_le univ fun i : n => charmatrix M (c i) i) _ 
    rw [card_eq_sum_ones]
    rw [sum_filter]
    apply sum_le_sum 
    intros 
    apply charmatrix_apply_nat_degree_le

theorem charpoly_coeff_eq_prod_coeff_of_le {k : ℕ} (h : Fintype.card n - 1 ≤ k) :
  M.charpoly.coeff k = (∏i : n, X - C (M i i)).coeff k :=
  by 
    apply eq_of_sub_eq_zero 
    rw [←coeff_sub]
    apply Polynomial.coeff_eq_zero_of_degree_lt 
    apply lt_of_lt_of_leₓ (charpoly_sub_diagonal_degree_lt M) _ 
    rw [WithBot.coe_le_coe]
    apply h

theorem det_of_card_zero (h : Fintype.card n = 0) (M : Matrix n n R) : M.det = 1 :=
  by 
    rw [Fintype.card_eq_zero_iff] at h 
    suffices  : M = 1
    ·
      simp [this]
    ext i 
    exact h.elim i

-- error in LinearAlgebra.Matrix.Charpoly.Coeff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem charpoly_degree_eq_dim [nontrivial R] (M : matrix n n R) : «expr = »(M.charpoly.degree, fintype.card n) :=
begin
  by_cases [expr «expr = »(fintype.card n, 0)],
  { rw [expr h] [],
    unfold [ident charpoly] [],
    rw [expr det_of_card_zero] [],
    { simp [] [] [] [] [] [] },
    { assumption } },
  rw ["<-", expr sub_add_cancel M.charpoly «expr∏ , »((i : n), «expr - »(X, C (M i i)))] [],
  have [ident h1] [":", expr «expr = »(«expr∏ , »((i : n), «expr - »(X, C (M i i))).degree, fintype.card n)] [],
  { rw [expr degree_eq_iff_nat_degree_eq_of_pos] [],
    swap,
    apply [expr nat.pos_of_ne_zero h],
    rw [expr nat_degree_prod'] [],
    simp_rw [expr nat_degree_X_sub_C] [],
    unfold [ident fintype.card] [],
    simp [] [] [] [] [] [],
    simp_rw [expr (monic_X_sub_C _).leading_coeff] [],
    simp [] [] [] [] [] [] },
  rw [expr degree_add_eq_right_of_degree_lt] [],
  exact [expr h1],
  rw [expr h1] [],
  apply [expr lt_trans (charpoly_sub_diagonal_degree_lt M)],
  rw [expr with_bot.coe_lt_coe] [],
  rw ["<-", expr nat.pred_eq_sub_one] [],
  apply [expr nat.pred_lt],
  apply [expr h]
end

theorem charpoly_nat_degree_eq_dim [Nontrivial R] (M : Matrix n n R) : M.charpoly.nat_degree = Fintype.card n :=
  nat_degree_eq_of_degree_eq_some (charpoly_degree_eq_dim M)

-- error in LinearAlgebra.Matrix.Charpoly.Coeff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem charpoly_monic (M : matrix n n R) : M.charpoly.monic :=
begin
  nontriviality [] [],
  by_cases [expr «expr = »(fintype.card n, 0)],
  { rw ["[", expr charpoly, ",", expr det_of_card_zero h, "]"] [],
    apply [expr monic_one] },
  have [ident mon] [":", expr «expr∏ , »((i : n), «expr - »(X, C (M i i))).monic] [],
  { apply [expr monic_prod_of_monic univ (λ i : n, «expr - »(X, C (M i i)))],
    simp [] [] [] ["[", expr monic_X_sub_C, "]"] [] [] },
  rw ["<-", expr sub_add_cancel «expr∏ , »((i : n), «expr - »(X, C (M i i))) M.charpoly] ["at", ident mon],
  rw [expr monic] ["at", "*"],
  rw [expr leading_coeff_add_of_degree_lt] ["at", ident mon],
  rw ["<-", expr mon] [],
  rw [expr charpoly_degree_eq_dim] [],
  rw ["<-", expr neg_sub] [],
  rw [expr degree_neg] [],
  apply [expr lt_trans (charpoly_sub_diagonal_degree_lt M)],
  rw [expr with_bot.coe_lt_coe] [],
  rw ["<-", expr nat.pred_eq_sub_one] [],
  apply [expr nat.pred_lt],
  apply [expr h]
end

theorem trace_eq_neg_charpoly_coeff [Nonempty n] (M : Matrix n n R) :
  (trace n R R) M = -M.charpoly.coeff (Fintype.card n - 1) :=
  by 
    nontriviality 
    rw [charpoly_coeff_eq_prod_coeff_of_le]
    swap 
    rfl 
    rw [Fintype.card, prod_X_sub_C_coeff_card_pred univ fun i : n => M i i]
    simp 
    rw [←Fintype.card, Fintype.card_pos_iff]
    infer_instance

-- error in LinearAlgebra.Matrix.Charpoly.Coeff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mat_poly_equiv_eval
(M : matrix n n (polynomial R))
(r : R)
(i j : n) : «expr = »((mat_poly_equiv M).eval (scalar n r) i j, (M i j).eval r) :=
begin
  unfold [ident polynomial.eval] [],
  unfold [ident eval₂] [],
  transitivity [expr polynomial.sum (mat_poly_equiv M) (λ
    (e : exprℕ())
    (a : matrix n n R), «expr * »(a, «expr ^ »(scalar n r, e)) i j)],
  { unfold [ident polynomial.sum] [],
    rw [expr sum_apply] [],
    dsimp [] [] [] [],
    refl },
  { simp_rw ["[", "<-", expr ring_hom.map_pow, ",", "<-", expr (scalar.commute _ _).eq, "]"] [],
    simp [] [] ["only"] ["[", expr coe_scalar, ",", expr matrix.one_mul, ",", expr ring_hom.id_apply, ",", expr pi.smul_apply, ",", expr smul_eq_mul, ",", expr mul_eq_mul, ",", expr algebra.smul_mul_assoc, "]"] [] [],
    have [ident h] [":", expr ∀
     x : exprℕ(), «expr = »(λ
      (e : exprℕ())
      (a : R), «expr * »(«expr ^ »(r, e), a) x 0, 0)] [":=", expr by simp [] [] [] [] [] []],
    simp [] [] ["only"] ["[", expr polynomial.sum, ",", expr mat_poly_equiv_coeff_apply, ",", expr mul_comm, "]"] [] [],
    apply [expr (finset.sum_subset (support_subset_support_mat_poly_equiv _ _ _) _).symm],
    assume [binders (n hn h'n)],
    rw [expr not_mem_support_iff] ["at", ident h'n],
    simp [] [] ["only"] ["[", expr h'n, ",", expr zero_mul, "]"] [] [] }
end

theorem eval_det (M : Matrix n n (Polynomial R)) (r : R) :
  Polynomial.eval r M.det = (Polynomial.eval (scalar n r) (matPolyEquiv M)).det :=
  by 
    rw [Polynomial.eval, ←coe_eval₂_ring_hom, RingHom.map_det]
    apply congr_argₓ det 
    ext 
    symm 
    convert mat_poly_equiv_eval _ _ _ _

theorem det_eq_sign_charpoly_coeff (M : Matrix n n R) : M.det = (-1^Fintype.card n)*M.charpoly.coeff 0 :=
  by 
    rw [coeff_zero_eq_eval_zero, charpoly, eval_det, mat_poly_equiv_charmatrix, ←det_smul]
    simp 

end Matrix

variable{p : ℕ}[Fact p.prime]

theorem mat_poly_equiv_eq_X_pow_sub_C {K : Type _} (k : ℕ) [Field K] (M : Matrix n n K) :
  matPolyEquiv ((expand K k : Polynomial K →+* Polynomial K).mapMatrix (charmatrix (M^k))) = (X^k) - C (M^k) :=
  by 
    ext m 
    rw [coeff_sub, coeff_C, mat_poly_equiv_coeff_apply, RingHom.map_matrix_apply, Matrix.map_apply,
      AlgHom.coe_to_ring_hom, Dmatrix.sub_apply, coeff_X_pow]
    byCases' hij : i = j
    ·
      rw [hij, charmatrix_apply_eq, AlgHom.map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow, coeff_C]
      splitIfs with mp m0 <;> simp only [Matrix.one_apply_eq, Dmatrix.zero_apply]
    ·
      rw [charmatrix_apply_ne _ _ _ hij, AlgHom.map_neg, expand_C, coeff_neg, coeff_C]
      splitIfs with m0 mp <;>
        simp only [hij, zero_sub, Dmatrix.zero_apply, sub_zero, neg_zero, Matrix.one_apply_ne, Ne.def, not_false_iff]

-- error in LinearAlgebra.Matrix.Charpoly.Coeff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem finite_field.matrix.charpoly_pow_card
{K : Type*}
[field K]
[fintype K]
(M : matrix n n K) : «expr = »(«expr ^ »(M, fintype.card K).charpoly, M.charpoly) :=
begin
  casesI [expr (is_empty_or_nonempty n).symm] [],
  { cases [expr char_p.exists K] ["with", ident p, ident hp],
    letI [] [] [":=", expr hp],
    rcases [expr finite_field.card K p, "with", "⟨", "⟨", ident k, ",", ident kpos, "⟩", ",", "⟨", ident hp, ",", ident hk, "⟩", "⟩"],
    haveI [] [":", expr fact p.prime] [":=", expr ⟨hp⟩],
    dsimp [] [] [] ["at", ident hk],
    rw [expr hk] ["at", "*"],
    apply [expr (frobenius_inj (polynomial K) p).iterate k],
    repeat { rw [expr iterate_frobenius] [],
      rw ["<-", expr hk] [] },
    rw ["<-", expr finite_field.expand_card] [],
    unfold [ident charpoly] [],
    rw ["[", expr alg_hom.map_det, ",", "<-", expr coe_det_monoid_hom, ",", "<-", expr (det_monoid_hom : «expr →* »(matrix n n (polynomial K), polynomial K)).map_pow, "]"] [],
    apply [expr congr_arg det],
    refine [expr mat_poly_equiv.injective _],
    rw ["[", expr alg_equiv.map_pow, ",", expr mat_poly_equiv_charmatrix, ",", expr hk, ",", expr sub_pow_char_pow_of_commute, ",", "<-", expr C_pow, "]"] [],
    { exact [expr (id (mat_poly_equiv_eq_X_pow_sub_C «expr ^ »(p, k) M) : _)] },
    { exact [expr (C M).commute_X] } },
  { haveI [] [":", expr subsingleton (matrix n n K)] [":=", expr subsingleton_of_empty_right],
    exact [expr congr_arg _ (subsingleton.elim _ _)] }
end

-- error in LinearAlgebra.Matrix.Charpoly.Coeff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem zmod.charpoly_pow_card (M : matrix n n (zmod p)) : «expr = »(«expr ^ »(M, p).charpoly, M.charpoly) :=
by { have [ident h] [] [":=", expr finite_field.matrix.charpoly_pow_card M],
  rwa [expr zmod.card] ["at", ident h] }

theorem FiniteField.trace_pow_card {K : Type _} [Field K] [Fintype K] [Nonempty n] (M : Matrix n n K) :
  trace n K K (M^Fintype.card K) = (trace n K K M^Fintype.card K) :=
  by 
    rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, FiniteField.Matrix.charpoly_pow_card,
      FiniteField.pow_card]

-- error in LinearAlgebra.Matrix.Charpoly.Coeff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem zmod.trace_pow_card
{p : exprℕ()}
[fact p.prime]
[nonempty n]
(M : matrix n n (zmod p)) : «expr = »(trace n (zmod p) (zmod p) «expr ^ »(M, p), «expr ^ »(trace n (zmod p) (zmod p) M, p)) :=
by { have [ident h] [] [":=", expr finite_field.trace_pow_card M],
  rwa [expr zmod.card] ["at", ident h] }

namespace Matrix

theorem IsIntegral : IsIntegral R M :=
  ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

theorem minpoly_dvd_charpoly {K : Type _} [Field K] (M : Matrix n n K) : minpoly K M ∣ M.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly M)

end Matrix

section PowerBasis

open Algebra

/-- The characteristic polynomial of the map `λ x, a * x` is the minimal polynomial of `a`.

In combination with `det_eq_sign_charpoly_coeff` or `trace_eq_neg_charpoly_coeff`
and a bit of rewriting, this will allow us to conclude the
field norm resp. trace of `x` is the product resp. sum of `x`'s conjugates.
-/
theorem charpoly_left_mul_matrix {K S : Type _} [Field K] [CommRingₓ S] [Algebra K S] (h : PowerBasis K S) :
  (left_mul_matrix h.basis h.gen).charpoly = minpoly K h.gen :=
  by 
    apply minpoly.unique
    ·
      apply Matrix.charpoly_monic
    ·
      apply (left_mul_matrix _).injective_iff.mp (left_mul_matrix_injective h.basis)
      rw [←Polynomial.aeval_alg_hom_apply, aeval_self_charpoly]
    ·
      intro q q_monic root_q 
      rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin, degree_eq_nat_degree q_monic.ne_zero]
      apply with_bot.some_le_some.mpr 
      exact h.dim_le_nat_degree_of_root q_monic.ne_zero root_q

end PowerBasis

