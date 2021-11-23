import Mathbin.Data.Matrix.Basis 
import Mathbin.Data.Matrix.Dmatrix 
import Mathbin.LinearAlgebra.Matrix.Determinant 
import Mathbin.LinearAlgebra.Matrix.Trace 
import Mathbin.LinearAlgebra.Matrix.Reindex 
import Mathbin.Tactic.FieldSimp

/-!
# Transvections

Transvections are matrices of the form `1 + std_basis_matrix i j c`, where `std_basis_matrix i j c`
is the basic matrix with a `c` at position `(i, j)`. Multiplying by such a transvection on the left
(resp. on the right) amounts to adding `c` times the `j`-th row to to the `i`-th row
(resp `c` times the `i`-th column to the `j`-th column). Therefore, they are useful to present
algorithms operating on rows and columns.

Transvections are a special case of *elementary matrices* (according to most references, these also
contain the matrices exchanging rows, and the matrices multiplying a row by a constant).

We show that, over a field, any matrix can be written as `L ⬝ D ⬝ L'`, where `L` and `L'` are
products of transvections and `D` is diagonal. In other words, one can reduce a matrix to diagonal
form by operations on its rows and columns, a variant of Gauss' pivot algorithm.

## Main definitions and results

* `transvection i j c` is the matrix equal to `1 + std_basis_matrix i j c`.
* `transvection_struct n R` is a structure containing the data of `i, j, c` and a proof that
  `i ≠ j`. These are often easier to manipulate than straight matrices, especially in inductive
  arguments.

* `exists_list_transvec_mul_diagonal_mul_list_transvec` states that any matrix `M` over a field can
  be written in the form `t_1 ⬝ ... ⬝ t_k ⬝ D ⬝ t'_1 ⬝ ... ⬝ t'_l`, where `D` is diagonal and
  the `t_i`, `t'_j` are transvections.

* `diagonal_transvection_induction` shows that a property which is true for diagonal matrices and
  transvections, and invariant under product, is true for all matrices.
* `diagonal_transvection_induction_of_det_ne_zero` is the same statement over invertible matrices.

## Implementation details

The proof of the reduction results is done inductively on the size of the matrices, reducing an
`(r + 1) × (r + 1)` matrix to a matrix whose last row and column are zeroes, except possibly for
the last diagonal entry. This step is done as follows.

If all the coefficients on the last row and column are zero, there is nothing to do. Otherwise,
one can put a nonzero coefficient in the last diagonal entry by a row or column operation, and then
subtract this last diagonal entry from the other entries in the last row and column to make them
vanish.

This step is done in the type `fin r ⊕ unit`, where `fin r` is useful to choose arbitrarily some
order in which we cancel the coefficients, and the sum structure is useful to use the formalism of
block matrices.

To proceed with the induction, we reindex our matrices to reduce to the above situation.
-/


universe u₁ u₂

namespace Matrix

open_locale Matrix

variable(n p : Type _)(R : Type u₂){𝕜 : Type _}[Field 𝕜]

variable[DecidableEq n][DecidableEq p]

variable[CommRingₓ R]

section Transvection

variable{R n}(i j : n)

/-- The transvection matrix `transvection i j c` is equal to the identity plus `c` at position
`(i, j)`. Multiplying by it on the left (as in `transvection i j c ⬝ M`) corresponds to adding
`c` times the `j`-th line of `M` to its `i`-th line. Multiplying by it on the right corresponds
to adding `c` times the `i`-th column to the `j`-th column. -/
def transvection (c : R) : Matrix n n R :=
  1+Matrix.stdBasisMatrix i j c

@[simp]
theorem transvection_zero : transvection i j (0 : R) = 1 :=
  by 
    simp [transvection]

section 

variable[Fintype n]

/-- A transvection matrix is obtained from the identity by adding `c` times the `j`-th row to
the `i`-th row. -/
theorem update_row_eq_transvection (c : R) :
  update_row (1 : Matrix n n R) i ((1 : Matrix n n R) i+c • (1 : Matrix n n R) j) = transvection i j c :=
  by 
    ext a b 
    byCases' ha : i = a <;> byCases' hb : j = b
    ·
      simp only [update_row, transvection, ha, hb, Function.update_same, std_basis_matrix.apply_same, Pi.add_apply,
        one_apply_eq, Pi.smul_apply, mul_oneₓ, Algebra.id.smul_eq_mul]
    ·
      simp only [update_row, transvection, ha, hb, std_basis_matrix.apply_of_ne, Function.update_same, Pi.add_apply,
        Ne.def, not_false_iff, Pi.smul_apply, and_falseₓ, one_apply_ne, Algebra.id.smul_eq_mul, mul_zero]
    ·
      simp only [update_row, transvection, ha, Ne.symm ha, std_basis_matrix.apply_of_ne, add_zeroₓ,
        Algebra.id.smul_eq_mul, Function.update_noteq, Ne.def, not_false_iff, Dmatrix.add_apply, Pi.smul_apply,
        mul_zero, false_andₓ]
    ·
      simp only [update_row, transvection, ha, hb, Ne.symm ha, std_basis_matrix.apply_of_ne, add_zeroₓ,
        Algebra.id.smul_eq_mul, Function.update_noteq, Ne.def, not_false_iff, and_selfₓ, Dmatrix.add_apply,
        Pi.smul_apply, mul_zero]

theorem transvection_mul_transvection_same (h : i ≠ j) (c d : R) :
  transvection i j c ⬝ transvection i j d = transvection i j (c+d) :=
  by 
    simp [transvection, Matrix.add_mul, Matrix.mul_add, h, h.symm, add_smul, add_assocₓ, std_basis_matrix_add]

@[simp]
theorem transvection_mul_apply_same (b : n) (c : R) (M : Matrix n n R) : (transvection i j c ⬝ M) i b = M i b+c*M j b :=
  by 
    simp [transvection, Matrix.add_mul]

@[simp]
theorem mul_transvection_apply_same (a : n) (c : R) (M : Matrix n n R) : (M ⬝ transvection i j c) a j = M a j+c*M a i :=
  by 
    simp [transvection, Matrix.mul_add, mul_commₓ]

@[simp]
theorem transvection_mul_apply_of_ne (a b : n) (ha : a ≠ i) (c : R) (M : Matrix n n R) :
  (transvection i j c ⬝ M) a b = M a b :=
  by 
    simp [transvection, Matrix.add_mul, ha]

@[simp]
theorem mul_transvection_apply_of_ne (a b : n) (hb : b ≠ j) (c : R) (M : Matrix n n R) :
  (M ⬝ transvection i j c) a b = M a b :=
  by 
    simp [transvection, Matrix.mul_add, hb]

@[simp]
theorem det_transvection_of_ne (h : i ≠ j) (c : R) : det (transvection i j c) = 1 :=
  by 
    rw [←update_row_eq_transvection i j, det_update_row_add_smul_self _ h, det_one]

end 

variable(R n)

/-- A structure containing all the information from which one can build a nontrivial transvection.
This structure is easier to manipulate than transvections as one has a direct access to all the
relevant fields. -/
@[nolint has_inhabited_instance]
structure transvection_struct where 
  (i j : n)
  hij : i ≠ j 
  c : R

instance  [Nontrivial n] : Nonempty (transvection_struct n R) :=
  by 
    choose x y hxy using exists_pair_ne n 
    exact ⟨⟨x, y, hxy, 0⟩⟩

namespace TransvectionStruct

variable{R n}

/-- Associating to a `transvection_struct` the corresponding transvection matrix. -/
def to_matrix (t : transvection_struct n R) : Matrix n n R :=
  transvection t.i t.j t.c

@[simp]
theorem to_matrix_mk (i j : n) (hij : i ≠ j) (c : R) :
  transvection_struct.to_matrix ⟨i, j, hij, c⟩ = transvection i j c :=
  rfl

@[simp]
protected theorem det [Fintype n] (t : transvection_struct n R) : det t.to_matrix = 1 :=
  det_transvection_of_ne _ _ t.hij _

@[simp]
theorem det_to_matrix_prod [Fintype n] (L : List (transvection_struct n 𝕜)) : det (L.map to_matrix).Prod = 1 :=
  by 
    induction' L with t L IH
    ·
      simp 
    ·
      simp [IH]

/-- The inverse of a `transvection_struct`, designed so that `t.inv.to_matrix` is the inverse of
`t.to_matrix`. -/
@[simps]
protected def inv (t : transvection_struct n R) : transvection_struct n R :=
  { i := t.i, j := t.j, hij := t.hij, c := -t.c }

section 

variable[Fintype n]

theorem inv_mul (t : transvection_struct n R) : t.inv.to_matrix ⬝ t.to_matrix = 1 :=
  by 
    rcases t with ⟨⟩
    simp [to_matrix, transvection_mul_transvection_same, t_hij]

theorem mul_inv (t : transvection_struct n R) : t.to_matrix ⬝ t.inv.to_matrix = 1 :=
  by 
    rcases t with ⟨⟩
    simp [to_matrix, transvection_mul_transvection_same, t_hij]

theorem reverse_inv_prod_mul_prod (L : List (transvection_struct n R)) :
  (L.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod ⬝ (L.map to_matrix).Prod = 1 :=
  by 
    induction' L with t L IH
    ·
      simp 
    ·
      suffices  :
        (L.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod ⬝ (t.inv.to_matrix ⬝ t.to_matrix) ⬝
            (L.map to_matrix).Prod =
          1
      ·
        simpa [Matrix.mul_assoc]
      simpa [inv_mul] using IH

theorem prod_mul_reverse_inv_prod (L : List (transvection_struct n R)) :
  (L.map to_matrix).Prod ⬝ (L.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod = 1 :=
  by 
    induction' L with t L IH
    ·
      simp 
    ·
      suffices  :
        t.to_matrix ⬝ ((L.map to_matrix).Prod ⬝ (L.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod) ⬝
            t.inv.to_matrix =
          1
      ·
        simpa [Matrix.mul_assoc]
      simpRw [IH, Matrix.mul_one, t.mul_inv]

end 

variable(p)

open Sum

/-- Given a `transvection_struct` on `n`, define the corresponding `transvection_struct` on `n ⊕ p`
using the identity on `p`. -/
def sum_inl (t : transvection_struct n R) : transvection_struct (Sum n p) R :=
  { i := inl t.i, j := inl t.j,
    hij :=
      by 
        simp [t.hij],
    c := t.c }

theorem to_matrix_sum_inl (t : transvection_struct n R) : (t.sum_inl p).toMatrix = from_blocks t.to_matrix 0 0 1 :=
  by 
    cases t 
    ext a b 
    cases a <;> cases b
    ·
      byCases' h : a = b <;> simp [transvection_struct.sum_inl, transvection, h, std_basis_matrix]
    ·
      simp [transvection_struct.sum_inl, transvection]
    ·
      simp [transvection_struct.sum_inl, transvection]
    ·
      byCases' h : a = b <;> simp [transvection_struct.sum_inl, transvection, h]

@[simp]
theorem sum_inl_to_matrix_prod_mul [Fintype n] [Fintype p] (M : Matrix n n R) (L : List (transvection_struct n R))
  (N : Matrix p p R) :
  (L.map (to_matrix ∘ sum_inl p)).Prod ⬝ from_blocks M 0 0 N = from_blocks ((L.map to_matrix).Prod ⬝ M) 0 0 N :=
  by 
    induction' L with t L IH
    ·
      simp 
    ·
      simp [Matrix.mul_assoc, IH, to_matrix_sum_inl, from_blocks_multiply]

@[simp]
theorem mul_sum_inl_to_matrix_prod [Fintype n] [Fintype p] (M : Matrix n n R) (L : List (transvection_struct n R))
  (N : Matrix p p R) :
  from_blocks M 0 0 N ⬝ (L.map (to_matrix ∘ sum_inl p)).Prod = from_blocks (M ⬝ (L.map to_matrix).Prod) 0 0 N :=
  by 
    induction' L with t L IH generalizing M N
    ·
      simp 
    ·
      simp [IH, to_matrix_sum_inl, from_blocks_multiply]

variable{p}

/-- Given a `transvection_struct` on `n` and an equivalence between `n` and `p`, define the
corresponding `transvection_struct` on `p`. -/
def reindex_equiv (e : n ≃ p) (t : transvection_struct n R) : transvection_struct p R :=
  { i := e t.i, j := e t.j,
    hij :=
      by 
        simp [t.hij],
    c := t.c }

variable[Fintype n][Fintype p]

theorem to_matrix_reindex_equiv (e : n ≃ p) (t : transvection_struct n R) :
  (t.reindex_equiv e).toMatrix = reindex_alg_equiv R e t.to_matrix :=
  by 
    cases t 
    ext a b 
    simp only [reindex_equiv, transvection, mul_boole, Algebra.id.smul_eq_mul, to_matrix_mk, minor_apply, reindex_apply,
      Dmatrix.add_apply, Pi.smul_apply, reindex_alg_equiv_apply]
    byCases' ha : e t_i = a <;>
      byCases' hb : e t_j = b <;>
        byCases' hab : a = b <;> simp [ha, hb, hab, ←e.apply_eq_iff_eq_symm_apply, std_basis_matrix]

theorem to_matrix_reindex_equiv_prod (e : n ≃ p) (L : List (transvection_struct n R)) :
  (L.map (to_matrix ∘ reindex_equiv e)).Prod = reindex_alg_equiv R e (L.map to_matrix).Prod :=
  by 
    induction' L with t L IH
    ·
      simp 
    ·
      simp only [to_matrix_reindex_equiv, IH, Function.comp_app, List.prod_cons, mul_eq_mul, reindex_alg_equiv_apply,
        List.map]
      exact (reindex_alg_equiv_mul _ _ _ _).symm

end TransvectionStruct

end Transvection

/-!
# Reducing matrices by left and right multiplication by transvections

In this section, we show that any matrix can be reduced to diagonal form by left and right
multiplication by transvections (or, equivalently, by elementary operations on lines and columns).
The main step is to kill the last row and column of a matrix in `fin r ⊕ unit` with nonzero last
coefficient, by subtracting this coefficient from the other ones. The list of these operations is
recorded in `list_transvec_col M` and `list_transvec_row M`. We have to analyze inductively how
these operations affect the coefficients in the last row and the last column to conclude that they
have the desired effect.

Once this is done, one concludes the reduction by induction on the size
of the matrices, through a suitable reindexing to identify any fintype with `fin r ⊕ unit`.
-/


namespace Pivot

variable{R}{r : ℕ}(M : Matrix (Sum (Finₓ r) Unit) (Sum (Finₓ r) Unit) 𝕜)

open Sum Unit Finₓ TransvectionStruct

/-- A list of transvections such that multiplying on the left with these transvections will replace
the last column with zeroes. -/
def list_transvec_col : List (Matrix (Sum (Finₓ r) Unit) (Sum (Finₓ r) Unit) 𝕜) :=
  List.ofFn$ fun i : Finₓ r => transvection (inl i) (inr star)$ -M (inl i) (inr star) / M (inr star) (inr star)

/-- A list of transvections such that multiplying on the right with these transvections will replace
the last row with zeroes. -/
def list_transvec_row : List (Matrix (Sum (Finₓ r) Unit) (Sum (Finₓ r) Unit) 𝕜) :=
  List.ofFn$ fun i : Finₓ r => transvection (inr star) (inl i)$ -M (inr star) (inl i) / M (inr star) (inr star)

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Multiplying by some of the matrices in `list_transvec_col M` does not change the last row. -/
theorem list_transvec_col_mul_last_row_drop
(i : «expr ⊕ »(fin r, unit))
{k : exprℕ()}
(hk : «expr ≤ »(k, r)) : «expr = »(«expr ⬝ »(((list_transvec_col M).drop k).prod, M) (inr star) i, M (inr star) i) :=
begin
  apply [expr nat.decreasing_induction' _ hk],
  { simp [] [] ["only"] ["[", expr list_transvec_col, ",", expr list.length_of_fn, ",", expr matrix.one_mul, ",", expr list.drop_eq_nil_of_le, ",", expr list.prod_nil, "]"] [] [] },
  { assume [binders (n hn hk IH)],
    have [ident hn'] [":", expr «expr < »(n, (list_transvec_col M).length)] [],
    by simpa [] [] [] ["[", expr list_transvec_col, "]"] [] ["using", expr hn],
    rw ["<-", expr list.cons_nth_le_drop_succ hn'] [],
    simpa [] [] [] ["[", expr list_transvec_col, ",", expr matrix.mul_assoc, "]"] [] [] }
end

/-- Multiplying by all the matrices in `list_transvec_col M` does not change the last row. -/
theorem list_transvec_col_mul_last_row (i : Sum (Finₓ r) Unit) :
  ((list_transvec_col M).Prod ⬝ M) (inr star) i = M (inr star) i :=
  by 
    simpa using list_transvec_col_mul_last_row_drop M i (zero_le _)

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Multiplying by all the matrices in `list_transvec_col M` kills all the coefficients in the
last column but the last one. -/
theorem list_transvec_col_mul_last_col
(hM : «expr ≠ »(M (inr star) (inr star), 0))
(i : fin r) : «expr = »(«expr ⬝ »((list_transvec_col M).prod, M) (inl i) (inr star), 0) :=
begin
  suffices [ident H] [":", expr ∀
   k : exprℕ(), «expr ≤ »(k, r) → «expr = »(«expr ⬝ »(((list_transvec_col M).drop k).prod, M) (inl i) (inr star), if «expr ≤ »(k, i) then 0 else M (inl i) (inr star))],
  by simpa [] [] ["only"] ["[", expr if_true, ",", expr list.drop.equations._eqn_1, "]"] [] ["using", expr H 0 (zero_le _)],
  assume [binders (k hk)],
  apply [expr nat.decreasing_induction' _ hk],
  { simp [] [] ["only"] ["[", expr list_transvec_col, ",", expr list.length_of_fn, ",", expr matrix.one_mul, ",", expr list.drop_eq_nil_of_le, ",", expr list.prod_nil, "]"] [] [],
    rw [expr if_neg] [],
    simpa [] [] ["only"] ["[", expr not_le, "]"] [] ["using", expr i.2] },
  { assume [binders (n hn hk IH)],
    have [ident hn'] [":", expr «expr < »(n, (list_transvec_col M).length)] [],
    by simpa [] [] [] ["[", expr list_transvec_col, "]"] [] ["using", expr hn],
    let [ident n'] [":", expr fin r] [":=", expr ⟨n, hn⟩],
    rw ["<-", expr list.cons_nth_le_drop_succ hn'] [],
    have [ident A] [":", expr «expr = »((list_transvec_col M).nth_le n hn', transvection (inl n') (inr star) «expr / »(«expr- »(M (inl n') (inr star)), M (inr star) (inr star)))] [],
    by simp [] [] [] ["[", expr list_transvec_col, "]"] [] [],
    simp [] [] ["only"] ["[", expr matrix.mul_assoc, ",", expr A, ",", expr matrix.mul_eq_mul, ",", expr list.prod_cons, "]"] [] [],
    by_cases [expr h, ":", expr «expr = »(n', i)],
    { have [ident hni] [":", expr «expr = »(n, i)] [],
      { cases [expr i] [],
        simp [] [] ["only"] ["[", expr subtype.mk_eq_mk, "]"] [] ["at", ident h],
        simp [] [] [] ["[", expr h, "]"] [] [] },
      rw ["[", expr h, ",", expr transvection_mul_apply_same, ",", expr IH, ",", expr list_transvec_col_mul_last_row_drop _ _ hn, ",", "<-", expr hni, "]"] [],
      field_simp [] ["[", expr hM, "]"] [] [] },
    { have [ident hni] [":", expr «expr ≠ »(n, i)] [],
      { rintros [ident rfl],
        cases [expr i] [],
        simpa [] [] [] [] [] ["using", expr h] },
      simp [] [] ["only"] ["[", expr transvection_mul_apply_of_ne, ",", expr ne.def, ",", expr not_false_iff, ",", expr ne.symm h, "]"] [] [],
      rw [expr IH] [],
      rcases [expr le_or_lt «expr + »(n, 1) i, "with", ident hi, "|", ident hi],
      { simp [] [] ["only"] ["[", expr hi, ",", expr n.le_succ.trans hi, ",", expr if_true, "]"] [] [] },
      { rw ["[", expr if_neg, ",", expr if_neg, "]"] [],
        { simpa [] [] ["only"] ["[", expr hni.symm, ",", expr not_le, ",", expr or_false, "]"] [] ["using", expr nat.lt_succ_iff_lt_or_eq.1 hi] },
        { simpa [] [] ["only"] ["[", expr not_le, "]"] [] ["using", expr hi] } } } }
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Multiplying by some of the matrices in `list_transvec_row M` does not change the last column. -/
theorem mul_list_transvec_row_last_col_take
(i : «expr ⊕ »(fin r, unit))
{k : exprℕ()}
(hk : «expr ≤ »(k, r)) : «expr = »(«expr ⬝ »(M, ((list_transvec_row M).take k).prod) i (inr star), M i (inr star)) :=
begin
  induction [expr k] [] ["with", ident k, ident IH] [],
  { simp [] [] ["only"] ["[", expr matrix.mul_one, ",", expr list.take_zero, ",", expr list.prod_nil, "]"] [] [] },
  { have [ident hkr] [":", expr «expr < »(k, r)] [":=", expr hk],
    let [ident k'] [":", expr fin r] [":=", expr ⟨k, hkr⟩],
    have [] [":", expr «expr = »((list_transvec_row M).nth k, «expr↑ »(transvection (inr unit.star) (inl k') «expr / »(«expr- »(M (inr unit.star) (inl k')), M (inr unit.star) (inr unit.star))))] [],
    { simp [] [] ["only"] ["[", expr list_transvec_row, ",", expr list.of_fn_nth_val, ",", expr hkr, ",", expr dif_pos, ",", expr list.nth_of_fn, "]"] [] [],
      refl },
    simp [] [] ["only"] ["[", expr list.take_succ, ",", "<-", expr matrix.mul_assoc, ",", expr this, ",", expr list.prod_append, ",", expr matrix.mul_one, ",", expr matrix.mul_eq_mul, ",", expr list.prod_cons, ",", expr list.prod_nil, ",", expr option.to_list_some, "]"] [] [],
    rw ["[", expr mul_transvection_apply_of_ne, ",", expr IH hkr.le, "]"] [],
    simp [] [] ["only"] ["[", expr ne.def, ",", expr not_false_iff, "]"] [] [] }
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Multiplying by all the matrices in `list_transvec_row M` does not change the last column. -/
theorem mul_list_transvec_row_last_col
(i : «expr ⊕ »(fin r, unit)) : «expr = »(«expr ⬝ »(M, (list_transvec_row M).prod) i (inr star), M i (inr star)) :=
begin
  have [ident A] [":", expr «expr = »((list_transvec_row M).length, r)] [],
  by simp [] [] [] ["[", expr list_transvec_row, "]"] [] [],
  rw ["[", "<-", expr list.take_length (list_transvec_row M), ",", expr A, "]"] [],
  simpa [] [] [] [] [] ["using", expr mul_list_transvec_row_last_col_take M i le_rfl]
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Multiplying by all the matrices in `list_transvec_row M` kills all the coefficients in the
last row but the last one. -/
theorem mul_list_transvec_row_last_row
(hM : «expr ≠ »(M (inr star) (inr star), 0))
(i : fin r) : «expr = »(«expr ⬝ »(M, (list_transvec_row M).prod) (inr star) (inl i), 0) :=
begin
  suffices [ident H] [":", expr ∀
   k : exprℕ(), «expr ≤ »(k, r) → «expr = »(«expr ⬝ »(M, ((list_transvec_row M).take k).prod) (inr star) (inl i), if «expr ≤ »(k, i) then M (inr star) (inl i) else 0)],
  { have [ident A] [":", expr «expr = »((list_transvec_row M).length, r)] [],
    by simp [] [] [] ["[", expr list_transvec_row, "]"] [] [],
    rw ["[", "<-", expr list.take_length (list_transvec_row M), ",", expr A, "]"] [],
    have [] [":", expr «expr¬ »(«expr ≤ »(r, i))] [],
    by simpa [] [] [] [] [] ["using", expr i.2],
    simpa [] [] ["only"] ["[", expr this, ",", expr ite_eq_right_iff, "]"] [] ["using", expr H r le_rfl] },
  assume [binders (k hk)],
  induction [expr k] [] ["with", ident n, ident IH] [],
  { simp [] [] ["only"] ["[", expr if_true, ",", expr matrix.mul_one, ",", expr list.take_zero, ",", expr zero_le', ",", expr list.prod_nil, "]"] [] [] },
  { have [ident hnr] [":", expr «expr < »(n, r)] [":=", expr hk],
    let [ident n'] [":", expr fin r] [":=", expr ⟨n, hnr⟩],
    have [ident A] [":", expr «expr = »((list_transvec_row M).nth n, «expr↑ »(transvection (inr unit.star) (inl n') «expr / »(«expr- »(M (inr unit.star) (inl n')), M (inr unit.star) (inr unit.star))))] [],
    { simp [] [] ["only"] ["[", expr list_transvec_row, ",", expr list.of_fn_nth_val, ",", expr hnr, ",", expr dif_pos, ",", expr list.nth_of_fn, "]"] [] [],
      refl },
    simp [] [] ["only"] ["[", expr list.take_succ, ",", expr A, ",", "<-", expr matrix.mul_assoc, ",", expr list.prod_append, ",", expr matrix.mul_one, ",", expr matrix.mul_eq_mul, ",", expr list.prod_cons, ",", expr list.prod_nil, ",", expr option.to_list_some, "]"] [] [],
    by_cases [expr h, ":", expr «expr = »(n', i)],
    { have [ident hni] [":", expr «expr = »(n, i)] [],
      { cases [expr i] [],
        simp [] [] ["only"] ["[", expr subtype.mk_eq_mk, "]"] [] ["at", ident h],
        simp [] [] ["only"] ["[", expr h, ",", expr coe_mk, "]"] [] [] },
      have [] [":", expr «expr¬ »(«expr ≤ »(n.succ, i))] [],
      by simp [] [] ["only"] ["[", "<-", expr hni, ",", expr n.lt_succ_self, ",", expr not_le, "]"] [] [],
      simp [] [] ["only"] ["[", expr h, ",", expr mul_transvection_apply_same, ",", expr list.take, ",", expr if_false, ",", expr mul_list_transvec_row_last_col_take _ _ hnr.le, ",", expr hni.le, ",", expr this, ",", expr if_true, ",", expr IH hnr.le, "]"] [] [],
      field_simp [] ["[", expr hM, "]"] [] [] },
    { have [ident hni] [":", expr «expr ≠ »(n, i)] [],
      { rintros [ident rfl],
        cases [expr i] [],
        simpa [] [] [] [] [] ["using", expr h] },
      simp [] [] ["only"] ["[", expr IH hnr.le, ",", expr ne.def, ",", expr mul_transvection_apply_of_ne, ",", expr not_false_iff, ",", expr ne.symm h, "]"] [] [],
      rcases [expr le_or_lt «expr + »(n, 1) i, "with", ident hi, "|", ident hi],
      { simp [] [] [] ["[", expr hi, ",", expr n.le_succ.trans hi, ",", expr if_true, "]"] [] [] },
      { rw ["[", expr if_neg, ",", expr if_neg, "]"] [],
        { simpa [] [] ["only"] ["[", expr not_le, "]"] [] ["using", expr hi] },
        { simpa [] [] ["only"] ["[", expr hni.symm, ",", expr not_le, ",", expr or_false, "]"] [] ["using", expr nat.lt_succ_iff_lt_or_eq.1 hi] } } } }
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Multiplying by all the matrices either in `list_transvec_col M` and `list_transvec_row M` kills
all the coefficients in the last row but the last one. -/
theorem list_transvec_col_mul_mul_list_transvec_row_last_col
(hM : «expr ≠ »(M (inr star) (inr star), 0))
(i : fin r) : «expr = »(«expr ⬝ »(«expr ⬝ »((list_transvec_col M).prod, M), (list_transvec_row M).prod) (inr star) (inl i), 0) :=
begin
  have [] [":", expr «expr = »(list_transvec_row M, list_transvec_row «expr ⬝ »((list_transvec_col M).prod, M))] [],
  by simp [] [] [] ["[", expr list_transvec_row, ",", expr list_transvec_col_mul_last_row, "]"] [] [],
  rw [expr this] [],
  apply [expr mul_list_transvec_row_last_row],
  simpa [] [] [] ["[", expr list_transvec_col_mul_last_row, "]"] [] ["using", expr hM]
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Multiplying by all the matrices either in `list_transvec_col M` and `list_transvec_row M` kills
all the coefficients in the last column but the last one. -/
theorem list_transvec_col_mul_mul_list_transvec_row_last_row
(hM : «expr ≠ »(M (inr star) (inr star), 0))
(i : fin r) : «expr = »(«expr ⬝ »(«expr ⬝ »((list_transvec_col M).prod, M), (list_transvec_row M).prod) (inl i) (inr star), 0) :=
begin
  have [] [":", expr «expr = »(list_transvec_col M, list_transvec_col «expr ⬝ »(M, (list_transvec_row M).prod))] [],
  by simp [] [] [] ["[", expr list_transvec_col, ",", expr mul_list_transvec_row_last_col, "]"] [] [],
  rw ["[", expr this, ",", expr matrix.mul_assoc, "]"] [],
  apply [expr list_transvec_col_mul_last_col],
  simpa [] [] [] ["[", expr mul_list_transvec_row_last_col, "]"] [] ["using", expr hM]
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Multiplying by all the matrices either in `list_transvec_col M` and `list_transvec_row M` turns
the matrix in block-diagonal form. -/
theorem is_two_block_diagonal_list_transvec_col_mul_mul_list_transvec_row
(hM : «expr ≠ »(M (inr star) (inr star), 0)) : is_two_block_diagonal «expr ⬝ »(«expr ⬝ »((list_transvec_col M).prod, M), (list_transvec_row M).prod) :=
begin
  split,
  { ext [] [ident i, ident j] [],
    have [] [":", expr «expr = »(j, star)] [],
    by simp [] [] ["only"] ["[", expr eq_iff_true_of_subsingleton, "]"] [] [],
    simp [] [] [] ["[", expr to_blocks₁₂, ",", expr this, ",", expr list_transvec_col_mul_mul_list_transvec_row_last_row M hM, "]"] [] [] },
  { ext [] [ident i, ident j] [],
    have [] [":", expr «expr = »(i, star)] [],
    by simp [] [] ["only"] ["[", expr eq_iff_true_of_subsingleton, "]"] [] [],
    simp [] [] [] ["[", expr to_blocks₂₁, ",", expr this, ",", expr list_transvec_col_mul_mul_list_transvec_row_last_col M hM, "]"] [] [] }
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- There exist two lists of `transvection_struct` such that multiplying by them on the left and
on the right makes a matrix block-diagonal, when the last coefficient is nonzero. -/
theorem exists_is_two_block_diagonal_of_ne_zero
(hM : «expr ≠ »(M (inr star) (inr star), 0)) : «expr∃ , »((L
  L' : list (transvection_struct «expr ⊕ »(fin r, unit) 𝕜)), is_two_block_diagonal «expr ⬝ »(«expr ⬝ »((L.map to_matrix).prod, M), (L'.map to_matrix).prod)) :=
begin
  let [ident L] [":", expr list (transvection_struct «expr ⊕ »(fin r, unit) 𝕜)] [":=", expr list.of_fn (λ
    i : fin r, ⟨inl i, inr star, by simp [] [] [] [] [] [], «expr / »(«expr- »(M (inl i) (inr star)), M (inr star) (inr star))⟩)],
  let [ident L'] [":", expr list (transvection_struct «expr ⊕ »(fin r, unit) 𝕜)] [":=", expr list.of_fn (λ
    i : fin r, ⟨inr star, inl i, by simp [] [] [] [] [] [], «expr / »(«expr- »(M (inr star) (inl i)), M (inr star) (inr star))⟩)],
  refine [expr ⟨L, L', _⟩],
  have [ident A] [":", expr «expr = »(L.map to_matrix, list_transvec_col M)] [],
  by simp [] [] [] ["[", expr L, ",", expr list_transvec_col, ",", expr («expr ∘ »), "]"] [] [],
  have [ident B] [":", expr «expr = »(L'.map to_matrix, list_transvec_row M)] [],
  by simp [] [] [] ["[", expr L, ",", expr list_transvec_row, ",", expr («expr ∘ »), "]"] [] [],
  rw ["[", expr A, ",", expr B, "]"] [],
  exact [expr is_two_block_diagonal_list_transvec_col_mul_mul_list_transvec_row M hM]
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- There exist two lists of `transvection_struct` such that multiplying by them on the left and
on the right makes a matrix block-diagonal. -/
theorem exists_is_two_block_diagonal_list_transvec_mul_mul_list_transvec
(M : matrix «expr ⊕ »(fin r, unit) «expr ⊕ »(fin r, unit) 𝕜) : «expr∃ , »((L
  L' : list (transvection_struct «expr ⊕ »(fin r, unit) 𝕜)), is_two_block_diagonal «expr ⬝ »(«expr ⬝ »((L.map to_matrix).prod, M), (L'.map to_matrix).prod)) :=
begin
  by_cases [expr H, ":", expr is_two_block_diagonal M],
  { refine [expr ⟨list.nil, list.nil, by simpa [] [] [] [] [] ["using", expr H]⟩] },
  by_cases [expr hM, ":", expr «expr ≠ »(M (inr star) (inr star), 0)],
  { exact [expr exists_is_two_block_diagonal_of_ne_zero M hM] },
  push_neg ["at", ident hM],
  simp [] [] [] ["[", expr not_and_distrib, ",", expr is_two_block_diagonal, ",", expr to_blocks₁₂, ",", expr to_blocks₂₁, "]"] [] ["at", ident H],
  have [] [":", expr «expr∃ , »((i : fin r), «expr ∨ »(«expr ≠ »(M (inl i) (inr star), 0), «expr ≠ »(M (inr star) (inl i), 0)))] [],
  { cases [expr H] [],
    { contrapose ["!"] [ident H],
      ext [] [ident i, ident j] [],
      convert [] [expr (H i).1] [],
      simp [] [] ["only"] ["[", expr eq_iff_true_of_subsingleton, "]"] [] [] },
    { contrapose ["!"] [ident H],
      ext [] [ident i, ident j] [],
      convert [] [expr (H j).2] [],
      simp [] [] ["only"] ["[", expr eq_iff_true_of_subsingleton, "]"] [] [] } },
  rcases [expr this, "with", "⟨", ident i, ",", ident h, "|", ident h, "⟩"],
  { let [ident M'] [] [":=", expr «expr ⬝ »(transvection (inr unit.star) (inl i) 1, M)],
    have [ident hM'] [":", expr «expr ≠ »(M' (inr star) (inr star), 0)] [],
    by simpa [] [] [] ["[", expr M', ",", expr hM, "]"] [] [],
    rcases [expr exists_is_two_block_diagonal_of_ne_zero M' hM', "with", "⟨", ident L, ",", ident L', ",", ident hLL', "⟩"],
    rw [expr matrix.mul_assoc] ["at", ident hLL'],
    refine [expr ⟨«expr ++ »(L, «expr[ , ]»([⟨inr star, inl i, by simp [] [] [] [] [] [], 1⟩])), L', _⟩],
    simp [] [] ["only"] ["[", expr list.map_append, ",", expr list.prod_append, ",", expr matrix.mul_one, ",", expr to_matrix_mk, ",", expr list.prod_cons, ",", expr list.prod_nil, ",", expr mul_eq_mul, ",", expr list.map, ",", expr matrix.mul_assoc (L.map to_matrix).prod, "]"] [] [],
    exact [expr hLL'] },
  { let [ident M'] [] [":=", expr «expr ⬝ »(M, transvection (inl i) (inr star) 1)],
    have [ident hM'] [":", expr «expr ≠ »(M' (inr star) (inr star), 0)] [],
    by simpa [] [] [] ["[", expr M', ",", expr hM, "]"] [] [],
    rcases [expr exists_is_two_block_diagonal_of_ne_zero M' hM', "with", "⟨", ident L, ",", ident L', ",", ident hLL', "⟩"],
    refine [expr ⟨L, [«expr :: »/«expr :: »/«expr :: »](⟨inl i, inr star, by simp [] [] [] [] [] [], 1⟩, L'), _⟩],
    simp [] [] ["only"] ["[", "<-", expr matrix.mul_assoc, ",", expr to_matrix_mk, ",", expr list.prod_cons, ",", expr mul_eq_mul, ",", expr list.map, "]"] [] [],
    rw ["[", expr matrix.mul_assoc (L.map to_matrix).prod, "]"] [],
    exact [expr hLL'] }
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Inductive step for the reduction: if one knows that any size `r` matrix can be reduced to
diagonal form by elementary operations, then one deduces it for matrices over `fin r ⊕ unit`. -/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction
(IH : ∀
 M : matrix (fin r) (fin r) 𝕜, «expr∃ , »((L₀ L₀' : list (transvection_struct (fin r) 𝕜))
  (D₀ : fin r → 𝕜), «expr = »(«expr ⬝ »(«expr ⬝ »((L₀.map to_matrix).prod, M), (L₀'.map to_matrix).prod), diagonal D₀)))
(M : matrix «expr ⊕ »(fin r, unit) «expr ⊕ »(fin r, unit) 𝕜) : «expr∃ , »((L
  L' : list (transvection_struct «expr ⊕ »(fin r, unit) 𝕜))
 (D : «expr ⊕ »(fin r, unit) → 𝕜), «expr = »(«expr ⬝ »(«expr ⬝ »((L.map to_matrix).prod, M), (L'.map to_matrix).prod), diagonal D)) :=
begin
  rcases [expr exists_is_two_block_diagonal_list_transvec_mul_mul_list_transvec M, "with", "⟨", ident L₁, ",", ident L₁', ",", ident hM, "⟩"],
  let [ident M'] [] [":=", expr «expr ⬝ »(«expr ⬝ »((L₁.map to_matrix).prod, M), (L₁'.map to_matrix).prod)],
  let [ident M''] [] [":=", expr to_blocks₁₁ M'],
  rcases [expr IH M'', "with", "⟨", ident L₀, ",", ident L₀', ",", ident D₀, ",", ident h₀, "⟩"],
  set [] [ident c] [] [":="] [expr M' (inr star) (inr star)] ["with", ident hc],
  refine [expr ⟨«expr ++ »(L₀.map (sum_inl unit), L₁), «expr ++ »(L₁', L₀'.map (sum_inl unit)), sum.elim D₀ (λ
     _, M' (inr star) (inr star)), _⟩],
  suffices [] [":", expr «expr = »(«expr ⬝ »(«expr ⬝ »((L₀.map «expr ∘ »(to_matrix, sum_inl unit)).prod, M'), (L₀'.map «expr ∘ »(to_matrix, sum_inl unit)).prod), diagonal (sum.elim D₀ (λ
      _, c)))],
  by simpa [] [] [] ["[", expr M', ",", expr matrix.mul_assoc, ",", expr c, "]"] [] [],
  have [] [":", expr «expr = »(M', from_blocks M'' 0 0 (diagonal (λ _, c)))] [],
  { rw ["<-", expr from_blocks_to_blocks M'] [],
    congr,
    { exact [expr hM.1] },
    { exact [expr hM.2] },
    { ext [] [ident i, ident j] [],
      rw ["[", expr hc, ",", expr to_blocks₂₂, "]"] [],
      congr } },
  rw [expr this] [],
  simp [] [] [] ["[", expr h₀, "]"] [] []
end

variable{n p}[Fintype n][Fintype p]

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Reduction to diagonal form by elementary operations is invariant under reindexing. -/
theorem reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal
(M : matrix p p 𝕜)
(e : «expr ≃ »(p, n))
(H : «expr∃ , »((L L' : list (transvection_struct n 𝕜))
  (D : n → 𝕜), «expr = »(«expr ⬝ »(«expr ⬝ »((L.map to_matrix).prod, matrix.reindex_alg_equiv 𝕜 e M), (L'.map to_matrix).prod), diagonal D))) : «expr∃ , »((L
  L' : list (transvection_struct p 𝕜))
 (D : p → 𝕜), «expr = »(«expr ⬝ »(«expr ⬝ »((L.map to_matrix).prod, M), (L'.map to_matrix).prod), diagonal D)) :=
begin
  rcases [expr H, "with", "⟨", ident L₀, ",", ident L₀', ",", ident D₀, ",", ident h₀, "⟩"],
  refine [expr ⟨L₀.map (reindex_equiv e.symm), L₀'.map (reindex_equiv e.symm), «expr ∘ »(D₀, e), _⟩],
  have [] [":", expr «expr = »(M, reindex_alg_equiv 𝕜 e.symm (reindex_alg_equiv 𝕜 e M))] [],
  by simp [] [] ["only"] ["[", expr equiv.symm_symm, ",", expr minor_minor, ",", expr reindex_apply, ",", expr minor_id_id, ",", expr equiv.symm_comp_self, ",", expr reindex_alg_equiv_apply, "]"] [] [],
  rw [expr this] [],
  simp [] [] ["only"] ["[", expr to_matrix_reindex_equiv_prod, ",", expr list.map_map, ",", expr reindex_alg_equiv_apply, "]"] [] [],
  simp [] [] ["only"] ["[", "<-", expr reindex_alg_equiv_apply, ",", "<-", expr reindex_alg_equiv_mul, ",", expr h₀, "]"] [] [],
  simp [] [] ["only"] ["[", expr equiv.symm_symm, ",", expr reindex_apply, ",", expr minor_diagonal_equiv, ",", expr reindex_alg_equiv_apply, "]"] [] []
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any matrix can be reduced to diagonal form by elementary operations. Formulated here on `Type 0`
because we will make an induction using `fin r`.
See `exists_list_transvec_mul_mul_list_transvec_eq_diagonal` for the general version (which follows
from this one and reindexing). -/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux
(n : Type)
[fintype n]
[decidable_eq n]
(M : matrix n n 𝕜) : «expr∃ , »((L L' : list (transvection_struct n 𝕜))
 (D : n → 𝕜), «expr = »(«expr ⬝ »(«expr ⬝ »((L.map to_matrix).prod, M), (L'.map to_matrix).prod), diagonal D)) :=
begin
  unfreezingI { induction [expr hn, ":", expr fintype.card n] [] ["with", ident r, ident IH] ["generalizing", ident n, ident M] },
  { refine [expr ⟨list.nil, list.nil, λ _, 1, _⟩],
    ext [] [ident i, ident j] [],
    rw [expr fintype.card_eq_zero_iff] ["at", ident hn],
    exact [expr hn.elim' i] },
  { have [ident e] [":", expr «expr ≃ »(n, «expr ⊕ »(fin r, unit))] [],
    { refine [expr fintype.equiv_of_card_eq _],
      rw [expr hn] [],
      convert [] [expr (@fintype.card_sum (fin r) unit _ _).symm] [],
      simp [] [] [] [] [] [] },
    apply [expr reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e],
    apply [expr exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction (λ
      N, IH (fin r) N (by simp [] [] [] [] [] []))] }
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any matrix can be reduced to diagonal form by elementary operations. -/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal
(M : matrix n n 𝕜) : «expr∃ , »((L L' : list (transvection_struct n 𝕜))
 (D : n → 𝕜), «expr = »(«expr ⬝ »(«expr ⬝ »((L.map to_matrix).prod, M), (L'.map to_matrix).prod), diagonal D)) :=
begin
  have [ident e] [":", expr «expr ≃ »(n, fin (fintype.card n))] [":=", expr fintype.equiv_of_card_eq (by simp [] [] [] [] [] [])],
  apply [expr reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e],
  apply [expr exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux]
end

/-- Any matrix can be written as the product of transvections, a diagonal matrix, and
transvections.-/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec (M : Matrix n n 𝕜) :
  ∃ (L L' : List (transvection_struct n 𝕜))(D : n → 𝕜),
    M = (L.map to_matrix).Prod ⬝ diagonal D ⬝ (L'.map to_matrix).Prod :=
  by 
    rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
    refine' ⟨L.reverse.map transvection_struct.inv, L'.reverse.map transvection_struct.inv, D, _⟩
    suffices  :
      M =
        (L.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod ⬝ (L.map to_matrix).Prod ⬝ M ⬝
          ((L'.map to_matrix).Prod ⬝ (L'.reverse.map (to_matrix ∘ transvection_struct.inv)).Prod)
    ·
      simpa [←h, Matrix.mul_assoc]
    rw [reverse_inv_prod_mul_prod, prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one]

end Pivot

open Pivot TransvectionStruct

variable{n}[Fintype n]

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Induction principle for matrices based on transvections: if a property is true for all diagonal
matrices, all transvections, and is stable under product, then it is true for all matrices. This is
the useful way to say that matrices are generated by diagonal matrices and transvections.

We state a slightly more general version: to prove a property for a matrix `M`, it suffices to
assume that the diagonal matrices we consider have the same determinant as `M`. This is useful to
obtain similar principles for `SLₙ` or `GLₙ`. -/
theorem diagonal_transvection_induction
(P : matrix n n 𝕜 → exprProp())
(M : matrix n n 𝕜)
(hdiag : ∀ D : n → 𝕜, «expr = »(det (diagonal D), det M) → P (diagonal D))
(htransvec : ∀ t : transvection_struct n 𝕜, P t.to_matrix)
(hmul : ∀ A B, P A → P B → P «expr ⬝ »(A, B)) : P M :=
begin
  rcases [expr exists_list_transvec_mul_diagonal_mul_list_transvec M, "with", "⟨", ident L, ",", ident L', ",", ident D, ",", ident h, "⟩"],
  have [ident PD] [":", expr P (diagonal D)] [":=", expr hdiag D (by simp [] [] [] ["[", expr h, "]"] [] [])],
  suffices [ident H] [":", expr ∀
   (L₁ L₂ : list (transvection_struct n 𝕜))
   (E : matrix n n 𝕜), P E → P «expr ⬝ »(«expr ⬝ »((L₁.map to_matrix).prod, E), (L₂.map to_matrix).prod)],
  by { rw [expr h] [],
    apply [expr H L L'],
    exact [expr PD] },
  assume [binders (L₁ L₂ E PE)],
  induction [expr L₁] [] ["with", ident t, ident L₁, ident IH] [],
  { simp [] [] ["only"] ["[", expr matrix.one_mul, ",", expr list.prod_nil, ",", expr list.map, "]"] [] [],
    induction [expr L₂] [] ["with", ident t, ident L₂, ident IH] ["generalizing", ident E],
    { simpa [] [] [] [] [] [] },
    { simp [] [] ["only"] ["[", "<-", expr matrix.mul_assoc, ",", expr list.prod_cons, ",", expr mul_eq_mul, ",", expr list.map, "]"] [] [],
      apply [expr IH],
      exact [expr hmul _ _ PE (htransvec _)] } },
  { simp [] [] ["only"] ["[", expr matrix.mul_assoc, ",", expr list.prod_cons, ",", expr mul_eq_mul, ",", expr list.map, "]"] [] ["at", "⊢", ident IH],
    exact [expr hmul _ _ (htransvec _) IH] }
end

-- error in LinearAlgebra.Matrix.Transvection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Induction principle for invertible matrices based on transvections: if a property is true for
all invertible diagonal matrices, all transvections, and is stable under product of invertible
matrices, then it is true for all invertible matrices. This is the useful way to say that
invertible matrices are generated by invertible diagonal matrices and transvections. -/
theorem diagonal_transvection_induction_of_det_ne_zero
(P : matrix n n 𝕜 → exprProp())
(M : matrix n n 𝕜)
(hMdet : «expr ≠ »(det M, 0))
(hdiag : ∀ D : n → 𝕜, «expr ≠ »(det (diagonal D), 0) → P (diagonal D))
(htransvec : ∀ t : transvection_struct n 𝕜, P t.to_matrix)
(hmul : ∀ A B, «expr ≠ »(det A, 0) → «expr ≠ »(det B, 0) → P A → P B → P «expr ⬝ »(A, B)) : P M :=
begin
  let [ident Q] [":", expr matrix n n 𝕜 → exprProp()] [":=", expr λ N, «expr ∧ »(«expr ≠ »(det N, 0), P N)],
  have [] [":", expr Q M] [],
  { apply [expr diagonal_transvection_induction Q M],
    { assume [binders (D hD)],
      have [ident detD] [":", expr «expr ≠ »(det (diagonal D), 0)] [],
      by { rw [expr hD] [],
        exact [expr hMdet] },
      exact [expr ⟨detD, hdiag _ detD⟩] },
    { assume [binders (t)],
      exact [expr ⟨by simp [] [] [] [] [] [], htransvec t⟩] },
    { assume [binders (A B QA QB)],
      exact [expr ⟨by simp [] [] [] ["[", expr QA.1, ",", expr QB.1, "]"] [] [], hmul A B QA.1 QB.1 QA.2 QB.2⟩] } },
  exact [expr this.2]
end

end Matrix

