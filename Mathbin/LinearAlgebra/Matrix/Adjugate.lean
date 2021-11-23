import Mathbin.Algebra.Associated 
import Mathbin.Algebra.Regular.Basic 
import Mathbin.LinearAlgebra.Matrix.MvPolynomial 
import Mathbin.LinearAlgebra.Matrix.Polynomial 
import Mathbin.RingTheory.Polynomial.Basic 
import Mathbin.Tactic.Linarith.Default 
import Mathbin.Tactic.RingExp

/-!
# Cramer's rule and adjugate matrices

The adjugate matrix is the transpose of the cofactor matrix.
It is calculated with Cramer's rule, which we introduce first.
The vectors returned by Cramer's rule are given by the linear map `cramer`,
which sends a matrix `A` and vector `b` to the vector consisting of the
determinant of replacing the `i`th column of `A` with `b` at index `i`
(written as `(A.update_column i b).det`).
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`.
The entries of the adjugate are the determinants of each minor of `A`.
Instead of defining a minor to be `A` with row `i` and column `j` deleted, we
replace the `i`th row of `A` with the `j`th basis vector; this has the same
determinant as the minor but more importantly equals Cramer's rule applied
to `A` and the `j`th basis vector, simplifying the subsequent proofs.
We prove the adjugate behaves like `det A • A⁻¹`.

## Main definitions

 * `matrix.cramer A b`: the vector output by Cramer's rule on `A` and `b`.
 * `matrix.adjugate A`: the adjugate (or classical adjoint) of the matrix `A`.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

cramer, cramer's rule, adjugate
-/


namespace Matrix

universe u v

variable{n : Type u}[DecidableEq n][Fintype n]{α : Type v}[CommRingₓ α]

open_locale Matrix BigOperators

open Equiv Equiv.Perm Finset

section Cramer

/-!
  ### `cramer` section

  Introduce the linear map `cramer` with values defined by `cramer_map`.
  After defining `cramer_map` and showing it is linear,
  we will restrict our proofs to using `cramer`.
-/


variable(A : Matrix n n α)(b : n → α)

/--
  `cramer_map A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer_map A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A ⬝ x = b` has a unique solution in `x`, `cramer_map A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer_map` is well-defined but not necessarily useful.
-/
def cramer_map (i : n) : α :=
  (A.update_column i b).det

theorem cramer_map_is_linear (i : n) : IsLinearMap α fun b => cramer_map A b i :=
  { map_add := det_update_column_add _ _, map_smul := det_update_column_smul _ _ }

theorem cramer_is_linear : IsLinearMap α (cramer_map A) :=
  by 
    split  <;> intros  <;> ext i
    ·
      apply (cramer_map_is_linear A i).1
    ·
      apply (cramer_map_is_linear A i).2

/--
  `cramer A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A ⬝ x = b` has a unique solution in `x`, `cramer A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer` is well-defined but not necessarily useful.
 -/
def cramer (A : Matrix n n α) : (n → α) →ₗ[α] n → α :=
  IsLinearMap.mk' (cramer_map A) (cramer_is_linear A)

theorem cramer_apply (i : n) : cramer A b i = (A.update_column i b).det :=
  rfl

theorem cramer_transpose_row_self (i : n) : (A)ᵀ.cramer (A i) = Pi.single i A.det :=
  by 
    ext j 
    rw [cramer_apply, Pi.single_apply]
    splitIfs with h
    ·
      subst h 
      simp only [update_column_transpose, det_transpose, update_row, Function.update_eq_self]
    ·
      rw [update_column_transpose, det_transpose]
      apply det_zero_of_row_eq h 
      rw [update_row_self, update_row_ne (Ne.symm h)]

theorem cramer_row_self (i : n) (h : ∀ j, b j = A j i) : A.cramer b = Pi.single i A.det :=
  by 
    rw [←transpose_transpose A, det_transpose]
    convert cramer_transpose_row_self (A)ᵀ i 
    exact funext h

@[simp]
theorem cramer_one : cramer (1 : Matrix n n α) = 1 :=
  by 
    ext i j 
    convert congr_funₓ (cramer_row_self (1 : Matrix n n α) (Pi.single i 1) i _) j
    ·
      simp 
    ·
      intro j 
      rw [Matrix.one_eq_pi_single, Pi.single_comm]

theorem cramer_smul (r : α) (A : Matrix n n α) : cramer (r • A) = (r^Fintype.card n - 1) • cramer A :=
  LinearMap.ext$ fun b => funext$ fun _ => det_update_column_smul' _ _ _ _

@[simp]
theorem cramer_subsingleton_apply [Subsingleton n] (A : Matrix n n α) (b : n → α) (i : n) : cramer A b i = b i :=
  by 
    rw [cramer_apply, det_eq_elem_of_subsingleton _ i, update_column_self]

theorem cramer_zero [Nontrivial n] : cramer (0 : Matrix n n α) = 0 :=
  by 
    ext i j 
    obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j 
    apply det_eq_zero_of_column_eq_zero j' 
    intro j'' 
    simp [update_column_ne hj']

/-- Use linearity of `cramer` to take it out of a summation. -/
theorem sum_cramer {β} (s : Finset β) (f : β → n → α) : (∑x in s, cramer A (f x)) = cramer A (∑x in s, f x) :=
  (LinearMap.map_sum (cramer A)).symm

/-- Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a summation. -/
theorem sum_cramer_apply {β} (s : Finset β) (f : n → β → α) (i : n) :
  (∑x in s, cramer A (fun j => f j x) i) = cramer A (fun j : n => ∑x in s, f j x) i :=
  calc (∑x in s, cramer A (fun j => f j x) i) = (∑x in s, cramer A fun j => f j x) i := (Finset.sum_apply i s _).symm 
    _ = cramer A (fun j : n => ∑x in s, f j x) i :=
    by 
      rw [sum_cramer, cramer_apply]
      congr with j 
      apply Finset.sum_apply
    

end Cramer

section Adjugate

/-!
### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring.
-/


/-- The adjugate matrix is the transpose of the cofactor matrix.

  Typically, the cofactor matrix is defined by taking the determinant of minors,
  i.e. the matrix with a row and column removed.
  However, the proof of `mul_adjugate` becomes a lot easier if we define the
  minor as replacing a column with a basis vector, since it allows us to use
  facts about the `cramer` map.
-/
def adjugate (A : Matrix n n α) : Matrix n n α :=
  fun i => cramer (A)ᵀ (Pi.single i 1)

theorem adjugate_def (A : Matrix n n α) : adjugate A = fun i => cramer (A)ᵀ (Pi.single i 1) :=
  rfl

theorem adjugate_apply (A : Matrix n n α) (i j : n) : adjugate A i j = (A.update_row j (Pi.single i 1)).det :=
  by 
    rw [adjugate_def]
    simp only 
    rw [cramer_apply, update_column_transpose, det_transpose]

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem adjugate_transpose (A : matrix n n α) : «expr = »(«expr ᵀ»(adjugate A), adjugate «expr ᵀ»(A)) :=
begin
  ext [] [ident i, ident j] [],
  rw ["[", expr transpose_apply, ",", expr adjugate_apply, ",", expr adjugate_apply, ",", expr update_row_transpose, ",", expr det_transpose, "]"] [],
  rw ["[", expr det_apply', ",", expr det_apply', "]"] [],
  apply [expr finset.sum_congr rfl],
  intros [ident σ, "_"],
  congr' [1] [],
  by_cases [expr «expr = »(i, σ j)],
  { congr; ext [] [ident j'] [],
    subst [expr h],
    have [] [":", expr «expr ↔ »(«expr = »(σ j', σ j), «expr = »(j', j))] [":=", expr σ.injective.eq_iff],
    rw ["[", expr update_row_apply, ",", expr update_column_apply, "]"] [],
    simp_rw [expr this] [],
    rw ["[", "<-", expr dite_eq_ite, ",", "<-", expr dite_eq_ite, "]"] [],
    congr' [1] ["with", ident rfl],
    rw ["[", expr pi.single_eq_same, ",", expr pi.single_eq_same, "]"] [] },
  { have [] [":", expr «expr = »(«expr∏ , »((j' : n), update_column A j (pi.single i 1) (σ j') j'), 0)] [],
    { apply [expr prod_eq_zero (mem_univ j)],
      rw ["[", expr update_column_self, ",", expr pi.single_eq_of_ne' h, "]"] [] },
    rw [expr this] [],
    apply [expr prod_eq_zero (mem_univ («expr ⁻¹»(σ) i))],
    erw ["[", expr apply_symm_apply σ i, ",", expr update_row_self, "]"] [],
    apply [expr pi.single_eq_of_ne],
    intro [ident h'],
    exact [expr h ((symm_apply_eq σ).mp h')] }
end

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Since the map `b ↦ cramer A b` is linear in `b`, it must be multiplication by some matrix. This
matrix is `A.adjugate`. -/
theorem cramer_eq_adjugate_mul_vec (A : matrix n n α) (b : n → α) : «expr = »(cramer A b, A.adjugate.mul_vec b) :=
begin
  nth_rewrite [1] ["<-", expr A.transpose_transpose] [],
  rw ["[", "<-", expr adjugate_transpose, ",", expr adjugate_def, "]"] [],
  have [] [":", expr «expr = »(b, «expr∑ , »((i), «expr • »(b i, pi.single i 1)))] [],
  { refine [expr (pi_eq_sum_univ b).trans _],
    congr' [] ["with", ident j],
    simp [] [] [] ["[", expr pi.single_apply, ",", expr eq_comm, "]"] [] [],
    congr },
  nth_rewrite [0] [expr this] [],
  ext [] [ident k] [],
  simp [] [] [] ["[", expr mul_vec, ",", expr dot_product, ",", expr mul_comm, "]"] [] []
end

theorem mul_adjugate_apply (A : Matrix n n α) i j k : (A i k*adjugate A k j) = cramer (A)ᵀ (Pi.single k (A i k)) j :=
  by 
    erw [←smul_eq_mul, ←Pi.smul_apply, ←LinearMap.map_smul, ←Pi.single_smul', smul_eq_mul, mul_oneₓ]

theorem mul_adjugate (A : Matrix n n α) : A ⬝ adjugate A = A.det • 1 :=
  by 
    ext i j 
    rw [mul_apply, Pi.smul_apply, Pi.smul_apply, one_apply, smul_eq_mul, mul_boole]
    simp [mul_adjugate_apply, sum_cramer_apply, cramer_transpose_row_self, Pi.single_apply, eq_comm]

theorem adjugate_mul (A : Matrix n n α) : adjugate A ⬝ A = A.det • 1 :=
  calc adjugate A ⬝ A = ((A)ᵀ ⬝ adjugate (A)ᵀ)ᵀ :=
    by 
      rw [←adjugate_transpose, ←transpose_mul, transpose_transpose]
    _ = A.det • 1 :=
    by 
      rw [mul_adjugate (A)ᵀ, det_transpose, transpose_smul, transpose_one]
    

theorem adjugate_smul (r : α) (A : Matrix n n α) : adjugate (r • A) = (r^Fintype.card n - 1) • adjugate A :=
  by 
    rw [adjugate, adjugate, transpose_smul, cramer_smul]
    rfl

/-- A stronger form of **Cramer's rule** that allows us to solve some instances of `A ⬝ x = b` even
if the determinant is not a unit. A sufficient (but still not necessary) condition is that `A.det`
divides `b`. -/
@[simp]
theorem mul_vec_cramer (A : Matrix n n α) (b : n → α) : A.mul_vec (cramer A b) = A.det • b :=
  by 
    rw [cramer_eq_adjugate_mul_vec, mul_vec_mul_vec, mul_adjugate, smul_mul_vec_assoc, one_mul_vec]

theorem adjugate_subsingleton [Subsingleton n] (A : Matrix n n α) : adjugate A = 1 :=
  by 
    ext i j 
    simp [Subsingleton.elimₓ i j, adjugate_apply, det_eq_elem_of_subsingleton _ i]

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem adjugate_eq_one_of_card_eq_one
{A : matrix n n α}
(h : «expr = »(fintype.card n, 1)) : «expr = »(adjugate A, 1) :=
begin
  haveI [] [":", expr subsingleton n] [":=", expr fintype.card_le_one_iff_subsingleton.mp h.le],
  exact [expr adjugate_subsingleton _]
end

@[simp]
theorem adjugate_zero [Nontrivial n] : adjugate (0 : Matrix n n α) = 0 :=
  by 
    ext i j 
    obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j 
    apply det_eq_zero_of_column_eq_zero j' 
    intro j'' 
    simp [update_column_ne hj']

@[simp]
theorem adjugate_one : adjugate (1 : Matrix n n α) = 1 :=
  by 
    ext 
    simp [adjugate_def, Matrix.one_apply, Pi.single_apply, eq_comm]

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem _root_.ring_hom.map_adjugate
{R S : Type*}
[comm_ring R]
[comm_ring S]
(f : «expr →+* »(R, S))
(M : matrix n n R) : «expr = »(f.map_matrix M.adjugate, matrix.adjugate (f.map_matrix M)) :=
begin
  ext [] [ident i, ident k] [],
  have [] [":", expr «expr = »(pi.single i (1 : S), «expr ∘ »(f, pi.single i 1))] [],
  { rw ["<-", expr f.map_one] [],
    exact [expr pi.single_op (λ i, f) (λ i, f.map_zero) i (1 : R)] },
  rw ["[", expr adjugate_apply, ",", expr ring_hom.map_matrix_apply, ",", expr map_apply, ",", expr ring_hom.map_matrix_apply, ",", expr this, ",", "<-", expr map_update_row, ",", "<-", expr ring_hom.map_matrix_apply, ",", "<-", expr ring_hom.map_det, ",", "<-", expr adjugate_apply, "]"] []
end

theorem _root_.alg_hom.map_adjugate {R A B : Type _} [CommSemiringₓ R] [CommRingₓ A] [CommRingₓ B] [Algebra R A]
  [Algebra R B] (f : A →ₐ[R] B) (M : Matrix n n A) : f.map_matrix M.adjugate = Matrix.adjugate (f.map_matrix M) :=
  f.to_ring_hom.map_adjugate _

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem det_adjugate (A : matrix n n α) : «expr = »((adjugate A).det, «expr ^ »(A.det, «expr - »(fintype.card n, 1))) :=
begin
  cases [expr (fintype.card n).eq_zero_or_pos] ["with", ident h_card, ident h_card],
  { haveI [] [":", expr is_empty n] [":=", expr fintype.card_eq_zero_iff.mp h_card],
    rw ["[", expr h_card, ",", expr nat.zero_sub, ",", expr pow_zero, ",", expr adjugate_subsingleton, ",", expr det_one, "]"] [] },
  replace [ident h_card] [] [":=", expr tsub_add_cancel_of_le h_card.nat_succ_le],
  let [ident A'] [] [":=", expr mv_polynomial_X n n exprℤ()],
  suffices [] [":", expr «expr = »(A'.adjugate.det, «expr ^ »(A'.det, «expr - »(fintype.card n, 1)))],
  { rw ["[", "<-", expr mv_polynomial_X_map_matrix_aeval exprℤ() A, ",", "<-", expr alg_hom.map_adjugate, ",", "<-", expr alg_hom.map_det, ",", "<-", expr alg_hom.map_det, ",", "<-", expr alg_hom.map_pow, ",", expr this, "]"] [] },
  apply [expr mul_left_cancel₀ (show «expr ≠ »(A'.det, 0), from det_mv_polynomial_X_ne_zero n exprℤ())],
  calc
    «expr = »(«expr * »(A'.det, A'.adjugate.det), «expr ⬝ »(A', adjugate A').det) : (det_mul _ _).symm
    «expr = »(..., «expr ^ »(A'.det, fintype.card n)) : by rw ["[", expr mul_adjugate, ",", expr det_smul, ",", expr det_one, ",", expr mul_one, "]"] []
    «expr = »(..., «expr * »(A'.det, «expr ^ »(A'.det, «expr - »(fintype.card n, 1)))) : by rw ["[", "<-", expr pow_succ, ",", expr h_card, "]"] []
end

@[simp]
theorem adjugate_fin_zero (A : Matrix (Finₓ 0) (Finₓ 0) α) : adjugate A = 0 :=
  @Subsingleton.elimₓ _ Matrix.subsingleton_of_empty_left _ _

@[simp]
theorem adjugate_fin_one (A : Matrix (Finₓ 1) (Finₓ 1) α) : adjugate A = 1 :=
  adjugate_subsingleton A

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr![ , ]»
theorem adjugate_fin_two
(A : matrix (fin 2) (fin 2) α) : «expr = »(adjugate A, «expr![ , ]»([«expr![ , ]»([A 1 1, «expr- »(A 0 1)]), «expr![ , ]»([«expr- »(A 1 0), A 0 0])])) :=
begin
  ext [] [ident i, ident j] [],
  rw ["[", expr adjugate_apply, ",", expr det_fin_two, "]"] [],
  fin_cases [ident i] ["with", expr «expr[ , ]»([0, 1])]; fin_cases [ident j] ["with", expr «expr[ , ]»([0, 1])]; simp [] [] ["only"] ["[", expr nat.one_ne_zero, ",", expr one_mul, ",", expr fin.one_eq_zero_iff, ",", expr pi.single_eq_same, ",", expr zero_mul, ",", expr fin.zero_eq_one_iff, ",", expr sub_zero, ",", expr pi.single_eq_of_ne, ",", expr ne.def, ",", expr not_false_iff, ",", expr update_row_self, ",", expr update_row_ne, ",", expr cons_val_zero, ",", expr mul_zero, ",", expr mul_one, ",", expr zero_sub, ",", expr cons_val_one, ",", expr head_cons, "]"] [] []
end

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr![ , ]»
@[simp]
theorem adjugate_fin_two'
(a
 b
 c
 d : α) : «expr = »(adjugate «expr![ , ]»([«expr![ , ]»([a, b]), «expr![ , ]»([c, d])]), «expr![ , ]»([«expr![ , ]»([d, «expr- »(b)]), «expr![ , ]»([«expr- »(c), a])])) :=
adjugate_fin_two _

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem adjugate_conj_transpose
[star_ring α]
(A : matrix n n α) : «expr = »(«expr ᴴ»(A.adjugate), adjugate «expr ᴴ»(A)) :=
begin
  dsimp ["only"] ["[", expr conj_transpose, "]"] [] [],
  have [] [":", expr «expr = »(«expr ᵀ»(A).adjugate.map star, adjugate («expr ᵀ»(A).map star))] [":=", expr (star_ring_aut : «expr ≃+* »(α, α)).to_ring_hom.map_adjugate «expr ᵀ»(A)],
  rw ["[", expr A.adjugate_transpose, ",", expr this, "]"] []
end

theorem is_regular_of_is_left_regular_det {A : Matrix n n α} (hA : IsLeftRegular A.det) : IsRegular A :=
  by 
    split 
    ·
      intro B C h 
      refine' hA.matrix _ 
      rw [←Matrix.one_mul B, ←Matrix.one_mul C, ←Matrix.smul_mul, ←Matrix.smul_mul, ←adjugate_mul, Matrix.mul_assoc,
        Matrix.mul_assoc, ←mul_eq_mul A, h, mul_eq_mul]
    ·
      intro B C h 
      simp only [mul_eq_mul] at h 
      refine' hA.matrix _ 
      rw [←Matrix.mul_one B, ←Matrix.mul_one C, ←Matrix.mul_smul, ←Matrix.mul_smul, ←mul_adjugate, ←Matrix.mul_assoc,
        ←Matrix.mul_assoc, h]

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem adjugate_mul_distrib_aux
(A B : matrix n n α)
(hA : is_left_regular A.det)
(hB : is_left_regular B.det) : «expr = »(adjugate «expr ⬝ »(A, B), «expr ⬝ »(adjugate B, adjugate A)) :=
begin
  have [ident hAB] [":", expr is_left_regular «expr ⬝ »(A, B).det] [],
  { rw ["[", expr det_mul, "]"] [],
    exact [expr hA.mul hB] },
  refine [expr (is_regular_of_is_left_regular_det hAB).left _],
  rw ["[", expr mul_eq_mul, ",", expr mul_adjugate, ",", expr mul_eq_mul, ",", expr matrix.mul_assoc, ",", "<-", expr matrix.mul_assoc B, ",", expr mul_adjugate, ",", expr smul_mul, ",", expr matrix.one_mul, ",", expr mul_smul, ",", expr mul_adjugate, ",", expr smul_smul, ",", expr mul_comm, ",", "<-", expr det_mul, "]"] []
end

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Proof follows from "The trace Cayley-Hamilton theorem" by Darij Grinberg, Section 5.3
-/
theorem adjugate_mul_distrib
(A B : matrix n n α) : «expr = »(adjugate «expr ⬝ »(A, B), «expr ⬝ »(adjugate B, adjugate A)) :=
begin
  casesI [expr subsingleton_or_nontrivial α] [],
  { simp [] [] [] [] [] [] },
  let [ident g] [":", expr matrix n n α → matrix n n (polynomial α)] [":=", expr λ
   M, «expr + »(M.map polynomial.C, «expr • »((polynomial.X : polynomial α), 1))],
  let [ident f'] [":", expr «expr →+* »(matrix n n (polynomial α), matrix n n α)] [":=", expr (polynomial.eval_ring_hom 0).map_matrix],
  have [ident f'_inv] [":", expr ∀ M, «expr = »(f' (g M), M)] [],
  { intro [],
    ext [] [] [],
    simp [] [] [] ["[", expr f', ",", expr g, "]"] [] [] },
  have [ident f'_adj] [":", expr ∀ M : matrix n n α, «expr = »(f' (adjugate (g M)), adjugate M)] [],
  { intro [],
    rw ["[", expr ring_hom.map_adjugate, ",", expr f'_inv, "]"] [] },
  have [ident f'_g_mul] [":", expr ∀ M N : matrix n n α, «expr = »(f' «expr ⬝ »(g M, g N), «expr ⬝ »(M, N))] [],
  { intros [],
    rw ["[", "<-", expr mul_eq_mul, ",", expr ring_hom.map_mul, ",", expr f'_inv, ",", expr f'_inv, ",", expr mul_eq_mul, "]"] [] },
  have [ident hu] [":", expr ∀ M : matrix n n α, is_regular (g M).det] [],
  { intros [ident M],
    refine [expr polynomial.monic.is_regular _],
    simp [] [] ["only"] ["[", expr g, ",", expr polynomial.monic.def, ",", "<-", expr polynomial.leading_coeff_det_X_one_add_C M, ",", expr add_comm, "]"] [] [] },
  rw ["[", "<-", expr f'_adj, ",", "<-", expr f'_adj, ",", "<-", expr f'_adj, ",", "<-", expr mul_eq_mul (f' (adjugate (g B))), ",", "<-", expr f'.map_mul, ",", expr mul_eq_mul, ",", "<-", expr adjugate_mul_distrib_aux _ _ (hu A).left (hu B).left, ",", expr ring_hom.map_adjugate, ",", expr ring_hom.map_adjugate, ",", expr f'_inv, ",", expr f'_g_mul, "]"] []
end

@[simp]
theorem adjugate_pow (A : Matrix n n α) (k : ℕ) : adjugate (A^k) = (adjugate A^k) :=
  by 
    induction' k with k IH
    ·
      simp 
    ·
      rw [pow_succ'ₓ, mul_eq_mul, adjugate_mul_distrib, IH, ←mul_eq_mul, pow_succₓ]

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem det_smul_adjugate_adjugate
(A : matrix n n α) : «expr = »(«expr • »(det A, adjugate (adjugate A)), «expr • »(«expr ^ »(det A, «expr - »(fintype.card n, 1)), A)) :=
begin
  have [] [":", expr «expr = »(«expr ⬝ »(A, «expr ⬝ »(A.adjugate, A.adjugate.adjugate)), «expr ⬝ »(A, «expr • »(«expr ^ »(A.det, «expr - »(fintype.card n, 1)), 1)))] [],
  { rw ["[", "<-", expr adjugate_mul_distrib, ",", expr adjugate_mul, ",", expr adjugate_smul, ",", expr adjugate_one, "]"] [] },
  rwa ["[", "<-", expr matrix.mul_assoc, ",", expr mul_adjugate, ",", expr matrix.mul_smul, ",", expr matrix.mul_one, ",", expr matrix.smul_mul, ",", expr matrix.one_mul, "]"] ["at", ident this]
end

-- error in LinearAlgebra.Matrix.Adjugate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Note that this is not true for `fintype.card n = 1` since `1 - 2 = 0` and not `-1`. -/
theorem adjugate_adjugate
(A : matrix n n α)
(h : «expr ≠ »(fintype.card n, 1)) : «expr = »(adjugate (adjugate A), «expr • »(«expr ^ »(det A, «expr - »(fintype.card n, 2)), A)) :=
begin
  cases [expr h_card, ":", expr fintype.card n] ["with", ident n'],
  { haveI [] [":", expr is_empty n] [":=", expr fintype.card_eq_zero_iff.mp h_card],
    exact [expr @subsingleton.elim _ matrix.subsingleton_of_empty_left _ _] },
  cases [expr n'] [],
  { exact [expr (h h_card).elim] },
  rw ["<-", expr h_card] [],
  let [ident A'] [] [":=", expr mv_polynomial_X n n exprℤ()],
  suffices [] [":", expr «expr = »(adjugate (adjugate A'), «expr • »(«expr ^ »(det A', «expr - »(fintype.card n, 2)), A'))],
  { rw ["[", "<-", expr mv_polynomial_X_map_matrix_aeval exprℤ() A, ",", "<-", expr alg_hom.map_adjugate, ",", "<-", expr alg_hom.map_adjugate, ",", expr this, ",", "<-", expr alg_hom.map_det, ",", "<-", expr alg_hom.map_pow, "]"] [],
    ext [] [ident i, ident j] [],
    dsimp [] ["[", "-", ident mv_polynomial_X, "]"] [] [],
    rw ["[", "<-", expr alg_hom.map_mul, "]"] [] },
  have [ident h_card'] [":", expr «expr = »(«expr + »(«expr - »(fintype.card n, 2), 1), «expr - »(fintype.card n, 1))] [],
  { simp [] [] [] ["[", expr h_card, "]"] [] [] },
  have [ident is_reg] [":", expr is_smul_regular (mv_polynomial «expr × »(n, n) exprℤ()) (det A')] [":=", expr λ
   x y, mul_left_cancel₀ (det_mv_polynomial_X_ne_zero n exprℤ())],
  apply [expr is_reg.matrix],
  rw ["[", expr smul_smul, ",", "<-", expr pow_succ, ",", expr h_card', ",", expr det_smul_adjugate_adjugate, "]"] []
end

/-- A weaker version of `matrix.adjugate_adjugate` that uses `nontrivial`. -/
theorem adjugate_adjugate' (A : Matrix n n α) [Nontrivial n] : adjugate (adjugate A) = (det A^Fintype.card n - 2) • A :=
  adjugate_adjugate _$ Fintype.one_lt_card.ne'

end Adjugate

end Matrix

