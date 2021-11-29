import Mathbin.Data.Matrix.Pequiv 
import Mathbin.Data.Matrix.Block 
import Mathbin.Data.Fintype.Card 
import Mathbin.GroupTheory.Perm.Fin 
import Mathbin.GroupTheory.Perm.Sign 
import Mathbin.Algebra.Algebra.Basic 
import Mathbin.Tactic.Ring 
import Mathbin.LinearAlgebra.Alternating 
import Mathbin.LinearAlgebra.Pi

/-!
# Determinant of a matrix

This file defines the determinant of a matrix, `matrix.det`, and its essential properties.

## Main definitions

 - `matrix.det`: the determinant of a square matrix, as a sum over permutations
 - `matrix.det_row_alternating`: the determinant, as an `alternating_map` in the rows of the matrix

## Main results

 - `det_mul`: the determinant of `A ⬝ B` is the product of determinants
 - `det_zero_of_row_eq`: the determinant is zero if there is a repeated row
 - `det_block_diagonal`: the determinant of a block diagonal matrix is a product
   of the blocks' determinants

## Implementation notes

It is possible to configure `simp` to compute determinants. See the file
`test/matrix.lean` for some examples.

-/


universe u v w z

open Equiv Equiv.Perm Finset Function

namespace Matrix

open_locale Matrix BigOperators

variable{m n : Type _}[DecidableEq n][Fintype n][DecidableEq m][Fintype m]

variable{R : Type v}[CommRingₓ R]

-- error in LinearAlgebra.Matrix.Determinant: ././Mathport/Syntax/Translate/Basic.lean:265:9: unsupported: advanced prec syntax
local notation `ε` σ:max := ((sign σ : exprℤ()) : R)

/-- `det` is an `alternating_map` in the rows of the matrix. -/
def det_row_alternating : AlternatingMap R (n → R) R n :=
  ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj).alternatization

/-- The determinant of a matrix given by the Leibniz formula. -/
abbrev det (M : Matrix n n R) : R :=
  det_row_alternating M

theorem det_apply (M : Matrix n n R) : M.det = ∑σ : perm n, σ.sign • ∏i, M (σ i) i :=
  MultilinearMap.alternatization_apply _ M

theorem det_apply' (M : Matrix n n R) : M.det = ∑σ : perm n, «exprε » σ*∏i, M (σ i) i :=
  by 
    simp [det_apply, Units.smul_def]

@[simp]
theorem det_diagonal {d : n → R} : det (diagonal d) = ∏i, d i :=
  by 
    rw [det_apply']
    refine' (Finset.sum_eq_single 1 _ _).trans _
    ·
      intro σ h1 h2 
      cases' not_forall.1 (mt Equiv.ext h2) with x h3 
      convert mul_zero _ 
      apply Finset.prod_eq_zero
      ·
        change x ∈ _ 
        simp 
      exact if_neg h3
    ·
      simp 
    ·
      simp 

@[simp]
theorem det_zero (h : Nonempty n) : det (0 : Matrix n n R) = 0 :=
  (det_row_alternating : AlternatingMap R (n → R) R n).map_zero

@[simp]
theorem det_one : det (1 : Matrix n n R) = 1 :=
  by 
    rw [←diagonal_one] <;> simp [-diagonal_one]

@[simp]
theorem det_is_empty [IsEmpty n] {A : Matrix n n R} : det A = 1 :=
  by 
    simp [det_apply]

-- error in LinearAlgebra.Matrix.Determinant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem det_eq_one_of_card_eq_zero {A : matrix n n R} (h : «expr = »(fintype.card n, 0)) : «expr = »(det A, 1) :=
begin
  haveI [] [":", expr is_empty n] [":=", expr fintype.card_eq_zero_iff.mp h],
  exact [expr det_is_empty]
end

/-- If `n` has only one element, the determinant of an `n` by `n` matrix is just that element.
Although `unique` implies `decidable_eq` and `fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
theorem det_unique {n : Type _} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) :
  det A = A (default n) (default n) :=
  by 
    simp [det_apply, univ_unique]

theorem det_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) : det A = A k k :=
  by 
    convert det_unique _ 
    exact uniqueOfSubsingleton k

-- error in LinearAlgebra.Matrix.Determinant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem det_eq_elem_of_card_eq_one
{A : matrix n n R}
(h : «expr = »(fintype.card n, 1))
(k : n) : «expr = »(det A, A k k) :=
begin
  haveI [] [":", expr subsingleton n] [":=", expr fintype.card_le_one_iff_subsingleton.mp h.le],
  exact [expr det_eq_elem_of_subsingleton _ _]
end

theorem det_mul_aux {M N : Matrix n n R} {p : n → n} (H : ¬bijective p) :
  (∑σ : perm n, «exprε » σ*∏x, M (σ x) (p x)*N (p x) x) = 0 :=
  by 
    obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j
    ·
      rw [←Fintype.injective_iff_bijective, injective] at H 
      pushNeg  at H 
      exact H 
    exact
      sum_involution (fun σ _ => σ*swap i j)
        (fun σ _ =>
          have  : (∏x, M (σ x) (p x)) = ∏x, M ((σ*swap i j) x) (p x) :=
            Fintype.prod_equiv (swap i j) _ _
              (by 
                simp [apply_swap_eq_self hpij])
          by 
            simp [this, sign_swap hij, prod_mul_distrib])
        (fun σ _ _ => (not_congr mul_swap_eq_iff).mpr hij) (fun _ _ => mem_univ _) fun σ _ => mul_swap_involutive i j σ

@[simp]
theorem det_mul (M N : Matrix n n R) : det (M ⬝ N) = det M*det N :=
  calc det (M ⬝ N) = ∑p : n → n, ∑σ : perm n, «exprε » σ*∏i, M (σ i) (p i)*N (p i) i :=
    by 
      simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.pi_finset_univ] <;> rw [Finset.sum_comm]
    _ = ∑p in (@univ (n → n) _).filter bijective, ∑σ : perm n, «exprε » σ*∏i, M (σ i) (p i)*N (p i) i :=
    Eq.symm$
      sum_subset (filter_subset _ _)
        fun f _ hbij =>
          det_mul_aux$
            by 
              simpa only [true_andₓ, mem_filter, mem_univ] using hbij 
    _ = ∑τ : perm n, ∑σ : perm n, «exprε » σ*∏i, M (σ i) (τ i)*N (τ i) i :=
    sum_bij (fun p h => Equiv.ofBijective p (mem_filter.1 h).2) (fun _ _ => mem_univ _) (fun _ _ => rfl)
      (fun _ _ _ _ h =>
        by 
          injection h)
      fun b _ => ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, coe_fn_injective rfl⟩
    _ = ∑σ : perm n, ∑τ : perm n, ((∏i, N (σ i) i)*«exprε » τ)*∏j, M (τ j) (σ j) :=
    by 
      simp only [mul_commₓ, mul_left_commₓ, prod_mul_distrib, mul_assocₓ]
    _ = ∑σ : perm n, ∑τ : perm n, ((∏i, N (σ i) i)*«exprε » σ*«exprε » τ)*∏i, M (τ i) i :=
    sum_congr rfl
      fun σ _ =>
        Fintype.sum_equiv (Equiv.mulRight (σ⁻¹)) _ _
          fun τ =>
            have  : (∏j, M (τ j) (σ j)) = ∏j, M ((τ*σ⁻¹) j) j :=
              by 
                rw [←σ⁻¹.prod_comp]
                simp only [Equiv.Perm.coe_mul, apply_inv_self]
            have h : («exprε » σ*«exprε » (τ*σ⁻¹)) = «exprε » τ :=
              calc («exprε » σ*«exprε » (τ*σ⁻¹)) = «exprε » ((τ*σ⁻¹)*σ) :=
                by 
                  rw [mul_commₓ, sign_mul (τ*σ⁻¹)]
                  simp only [Int.cast_mul, Units.coe_mul]
                _ = «exprε » τ :=
                by 
                  simp only [inv_mul_cancel_right]
                
            by 
              simpRw [Equiv.coe_mul_right, h]
              simp only [this]
    _ = det M*det N :=
    by 
      simp only [det_apply', Finset.mul_sum, mul_commₓ, mul_left_commₓ]
    

/-- The determinant of a matrix, as a monoid homomorphism. -/
def det_monoid_hom : Matrix n n R →* R :=
  { toFun := det, map_one' := det_one, map_mul' := det_mul }

@[simp]
theorem coe_det_monoid_hom : (det_monoid_hom : Matrix n n R → R) = det :=
  rfl

/-- On square matrices, `mul_comm` applies under `det`. -/
theorem det_mul_comm (M N : Matrix m m R) : det (M ⬝ N) = det (N ⬝ M) :=
  by 
    rw [det_mul, det_mul, mul_commₓ]

/-- On square matrices, `mul_left_comm` applies under `det`. -/
theorem det_mul_left_comm (M N P : Matrix m m R) : det (M ⬝ (N ⬝ P)) = det (N ⬝ (M ⬝ P)) :=
  by 
    rw [←Matrix.mul_assoc, ←Matrix.mul_assoc, det_mul, det_mul_comm M N, ←det_mul]

/-- On square matrices, `mul_right_comm` applies under `det`. -/
theorem det_mul_right_comm (M N P : Matrix m m R) : det (M ⬝ N ⬝ P) = det (M ⬝ P ⬝ N) :=
  by 
    rw [Matrix.mul_assoc, Matrix.mul_assoc, det_mul, det_mul_comm N P, ←det_mul]

theorem det_units_conj (M : Units (Matrix m m R)) (N : Matrix m m R) :
  det («expr↑ » M ⬝ N ⬝ «expr↑ » (M⁻¹) : Matrix m m R) = det N :=
  by 
    rw [det_mul_right_comm, ←mul_eq_mul, ←mul_eq_mul, Units.mul_inv, one_mulₓ]

theorem det_units_conj' (M : Units (Matrix m m R)) (N : Matrix m m R) :
  det («expr↑ » (M⁻¹) ⬝ N ⬝ «expr↑ » M : Matrix m m R) = det N :=
  det_units_conj (M⁻¹) N

/-- Transposing a matrix preserves the determinant. -/
@[simp]
theorem det_transpose (M : Matrix n n R) : (M)ᵀ.det = M.det :=
  by 
    rw [det_apply', det_apply']
    refine' Fintype.sum_bijective _ inv_involutive.bijective _ _ _ 
    intro σ 
    rw [sign_inv]
    congr 1
    apply Fintype.prod_equiv σ 
    intros 
    simp 

/-- Permuting the columns changes the sign of the determinant. -/
theorem det_permute (σ : perm n) (M : Matrix n n R) : (Matrix.det fun i => M (σ i)) = σ.sign*M.det :=
  ((det_row_alternating : AlternatingMap R (n → R) R n).map_perm M σ).trans
    (by 
      simp [Units.smul_def])

/-- Permuting rows and columns with the same equivalence has no effect. -/
@[simp]
theorem det_minor_equiv_self (e : n ≃ m) (A : Matrix m m R) : det (A.minor e e) = det A :=
  by 
    rw [det_apply', det_apply']
    apply Fintype.sum_equiv (Equiv.permCongr e)
    intro σ 
    rw [Equiv.Perm.sign_perm_congr e σ]
    congr 1
    apply Fintype.prod_equiv e 
    intro i 
    rw [Equiv.perm_congr_apply, Equiv.symm_apply_apply, minor_apply]

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_minor_equiv_self`; this one is unsuitable because
`matrix.reindex_apply` unfolds `reindex` first.
-/
theorem det_reindex_self (e : m ≃ n) (A : Matrix m m R) : det (reindex e e A) = det A :=
  det_minor_equiv_self e.symm A

/-- The determinant of a permutation matrix equals its sign. -/
@[simp]
theorem det_permutation (σ : perm n) : Matrix.det (σ.to_pequiv.to_matrix : Matrix n n R) = σ.sign :=
  by 
    rw [←Matrix.mul_one (σ.to_pequiv.to_matrix : Matrix n n R), Pequiv.to_pequiv_mul_matrix, det_permute, det_one,
      mul_oneₓ]

@[simp]
theorem det_smul (A : Matrix n n R) (c : R) : det (c • A) = (c^Fintype.card n)*det A :=
  calc det (c • A) = det (Matrix.mul (diagonal fun _ => c) A) :=
    by 
      rw [smul_eq_diagonal_mul]
    _ = det (diagonal fun _ => c)*det A := det_mul _ _ 
    _ = (c^Fintype.card n)*det A :=
    by 
      simp [card_univ]
    

/-- Multiplying each row by a fixed `v i` multiplies the determinant by
the product of the `v`s. -/
theorem det_mul_row (v : n → R) (A : Matrix n n R) : (det fun i j => v j*A i j) = (∏i, v i)*det A :=
  calc (det fun i j => v j*A i j) = det (A ⬝ diagonal v) :=
    congr_argₓ det$
      by 
        ext 
        simp [mul_commₓ]
    _ = (∏i, v i)*det A :=
    by 
      rw [det_mul, det_diagonal, mul_commₓ]
    

/-- Multiplying each column by a fixed `v j` multiplies the determinant by
the product of the `v`s. -/
theorem det_mul_column (v : n → R) (A : Matrix n n R) : (det fun i j => v i*A i j) = (∏i, v i)*det A :=
  MultilinearMap.map_smul_univ _ v A

@[simp]
theorem det_pow (M : Matrix m m R) (n : ℕ) : det (M^n) = (det M^n) :=
  (det_monoid_hom : Matrix m m R →* R).map_pow M n

section HomMap

variable{S : Type w}[CommRingₓ S]

theorem _root_.ring_hom.map_det (f : R →+* S) (M : Matrix n n R) : f M.det = Matrix.det (f.map_matrix M) :=
  by 
    simp [Matrix.det_apply', f.map_sum, f.map_prod]

theorem _root_.ring_equiv.map_det (f : R ≃+* S) (M : Matrix n n R) : f M.det = Matrix.det (f.map_matrix M) :=
  f.to_ring_hom.map_det _

theorem _root_.alg_hom.map_det [Algebra R S] {T : Type z} [CommRingₓ T] [Algebra R T] (f : S →ₐ[R] T)
  (M : Matrix n n S) : f M.det = Matrix.det (f.map_matrix M) :=
  f.to_ring_hom.map_det _

theorem _root_.alg_equiv.map_det [Algebra R S] {T : Type z} [CommRingₓ T] [Algebra R T] (f : S ≃ₐ[R] T)
  (M : Matrix n n S) : f M.det = Matrix.det (f.map_matrix M) :=
  f.to_alg_hom.map_det _

end HomMap

@[simp]
theorem det_conj_transpose [StarRing R] (M : Matrix m m R) : det (M)ᴴ = star (det M) :=
  ((starRingAut : RingAut R).map_det _).symm.trans$ congr_argₓ star M.det_transpose

section DetZero

/-!
### `det_zero` section

Prove that a matrix with a repeated column has determinant equal to zero.
-/


theorem det_eq_zero_of_row_eq_zero {A : Matrix n n R} (i : n) (h : ∀ j, A i j = 0) : det A = 0 :=
  (det_row_alternating : AlternatingMap R (n → R) R n).map_coord_zero i (funext h)

theorem det_eq_zero_of_column_eq_zero {A : Matrix n n R} (j : n) (h : ∀ i, A i j = 0) : det A = 0 :=
  by 
    rw [←det_transpose]
    exact det_eq_zero_of_row_eq_zero j h

variable{M : Matrix n n R}{i j : n}

/-- If a matrix has a repeated row, the determinant will be zero. -/
theorem det_zero_of_row_eq (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
  (det_row_alternating : AlternatingMap R (n → R) R n).map_eq_zero_of_eq M hij i_ne_j

/-- If a matrix has a repeated column, the determinant will be zero. -/
theorem det_zero_of_column_eq (i_ne_j : i ≠ j) (hij : ∀ k, M k i = M k j) : M.det = 0 :=
  by 
    rw [←det_transpose, det_zero_of_row_eq i_ne_j]
    exact funext hij

end DetZero

theorem det_update_row_add (M : Matrix n n R) (j : n) (u v : n → R) :
  det (update_row M j$ u+v) = det (update_row M j u)+det (update_row M j v) :=
  (det_row_alternating : AlternatingMap R (n → R) R n).map_add M j u v

theorem det_update_column_add (M : Matrix n n R) (j : n) (u v : n → R) :
  det (update_column M j$ u+v) = det (update_column M j u)+det (update_column M j v) :=
  by 
    rw [←det_transpose, ←update_row_transpose, det_update_row_add]
    simp [update_row_transpose, det_transpose]

theorem det_update_row_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
  det (update_row M j$ s • u) = s*det (update_row M j u) :=
  (det_row_alternating : AlternatingMap R (n → R) R n).map_smul M j s u

theorem det_update_column_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
  det (update_column M j$ s • u) = s*det (update_column M j u) :=
  by 
    rw [←det_transpose, ←update_row_transpose, det_update_row_smul]
    simp [update_row_transpose, det_transpose]

theorem det_update_row_smul' (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
  det (update_row (s • M) j u) = (s^Fintype.card n - 1)*det (update_row M j u) :=
  MultilinearMap.map_update_smul _ M j s u

theorem det_update_column_smul' (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
  det (update_column (s • M) j u) = (s^Fintype.card n - 1)*det (update_column M j u) :=
  by 
    rw [←det_transpose, ←update_row_transpose, transpose_smul, det_update_row_smul']
    simp [update_row_transpose, det_transpose]

section DetEq

/-! ### `det_eq` section

Lemmas showing the determinant is invariant under a variety of operations.
-/


theorem det_eq_of_eq_mul_det_one {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1) (hA : A = B ⬝ C) :
  det A = det B :=
  calc det A = det (B ⬝ C) := congr_argₓ _ hA 
    _ = det B*det C := det_mul _ _ 
    _ = det B :=
    by 
      rw [hC, mul_oneₓ]
    

theorem det_eq_of_eq_det_one_mul {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1) (hA : A = C ⬝ B) :
  det A = det B :=
  calc det A = det (C ⬝ B) := congr_argₓ _ hA 
    _ = det C*det B := det_mul _ _ 
    _ = det B :=
    by 
      rw [hC, one_mulₓ]
    

theorem det_update_row_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) : det (update_row A i (A i+A j)) = det A :=
  by 
    simp [det_update_row_add, det_zero_of_row_eq hij (update_row_self.trans (update_row_ne hij.symm).symm)]

theorem det_update_column_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
  det (update_column A i fun k => A k i+A k j) = det A :=
  by 
    rw [←det_transpose, ←update_row_transpose, ←det_transpose A]
    exact det_update_row_add_self (A)ᵀ hij

theorem det_update_row_add_smul_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
  det (update_row A i (A i+c • A j)) = det A :=
  by 
    simp [det_update_row_add, det_update_row_smul,
      det_zero_of_row_eq hij (update_row_self.trans (update_row_ne hij.symm).symm)]

theorem det_update_column_add_smul_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
  det (update_column A i fun k => A k i+c • A k j) = det A :=
  by 
    rw [←det_transpose, ←update_row_transpose, ←det_transpose A]
    exact det_update_row_add_smul_self (A)ᵀ hij c

-- error in LinearAlgebra.Matrix.Determinant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem det_eq_of_forall_row_eq_smul_add_const_aux
{A B : matrix n n R}
{s : finset n} : ∀
(c : n → R)
(hs : ∀ i, «expr ∉ »(i, s) → «expr = »(c i, 0))
(k : n)
(hk : «expr ∉ »(k, s))
(A_eq : ∀ i j, «expr = »(A i j, «expr + »(B i j, «expr * »(c i, B k j)))), «expr = »(det A, det B) :=
begin
  revert [ident B],
  refine [expr s.induction_on _ _],
  { intros [ident A, ident c, ident hs, ident k, ident hk, ident A_eq],
    have [] [":", expr ∀ i, «expr = »(c i, 0)] [],
    { intros [ident i],
      specialize [expr hs i],
      contrapose ["!"] [ident hs],
      simp [] [] [] ["[", expr hs, "]"] [] [] },
    congr,
    ext [] [ident i, ident j] [],
    rw ["[", expr A_eq, ",", expr this, ",", expr zero_mul, ",", expr add_zero, "]"] [] },
  { intros [ident i, ident s, ident hi, ident ih, ident B, ident c, ident hs, ident k, ident hk, ident A_eq],
    have [ident hAi] [":", expr «expr = »(A i, «expr + »(B i, «expr • »(c i, B k)))] [":=", expr funext (A_eq i)],
    rw ["[", expr @ih (update_row B i (A i)) (function.update c i 0), ",", expr hAi, ",", expr det_update_row_add_smul_self, "]"] [],
    { exact [expr mt (λ h, show «expr ∈ »(k, insert i s), from «expr ▸ »(h, finset.mem_insert_self _ _)) hk] },
    { intros [ident i', ident hi'],
      rw [expr function.update_apply] [],
      split_ifs [] ["with", ident hi'i],
      { refl },
      { exact [expr hs i' (λ h, hi' ((finset.mem_insert.mp h).resolve_left hi'i))] } },
    { exact [expr λ h, hk (finset.mem_insert_of_mem h)] },
    { intros [ident i', ident j'],
      rw ["[", expr update_row_apply, ",", expr function.update_apply, "]"] [],
      split_ifs [] ["with", ident hi'i],
      { simp [] [] [] ["[", expr hi'i, "]"] [] [] },
      rw ["[", expr A_eq, ",", expr update_row_ne (λ
        h : «expr = »(k, i), «expr $ »(hk, «expr ▸ »(h, finset.mem_insert_self k s))), "]"] [] } }
end

-- error in LinearAlgebra.Matrix.Determinant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If you add multiples of row `B k` to other rows, the determinant doesn't change. -/
theorem det_eq_of_forall_row_eq_smul_add_const
{A B : matrix n n R}
(c : n → R)
(k : n)
(hk : «expr = »(c k, 0))
(A_eq : ∀ i j, «expr = »(A i j, «expr + »(B i j, «expr * »(c i, B k j)))) : «expr = »(det A, det B) :=
det_eq_of_forall_row_eq_smul_add_const_aux c (λ
 i, «expr $ »(not_imp_comm.mp, λ
  hi, finset.mem_erase.mpr ⟨mt (λ
    h : «expr = »(i, k), show «expr = »(c i, 0), from «expr ▸ »(h.symm, hk)) hi, finset.mem_univ i⟩)) k (finset.not_mem_erase k finset.univ) A_eq

-- error in LinearAlgebra.Matrix.Determinant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem det_eq_of_forall_row_eq_smul_add_pred_aux
{n : exprℕ()}
(k : fin «expr + »(n, 1)) : ∀
(c : fin n → R)
(hc : ∀ i : fin n, «expr < »(k, i.succ) → «expr = »(c i, 0))
{M N : matrix (fin n.succ) (fin n.succ) R}
(h0 : ∀ j, «expr = »(M 0 j, N 0 j))
(hsucc : ∀
 (i : fin n)
 (j), «expr = »(M i.succ j, «expr + »(N i.succ j, «expr * »(c i, M i.cast_succ j)))), «expr = »(det M, det N) :=
begin
  refine [expr fin.induction _ (λ k ih, _) k]; intros [ident c, ident hc, ident M, ident N, ident h0, ident hsucc],
  { congr,
    ext [] [ident i, ident j] [],
    refine [expr fin.cases (h0 j) (λ i, _) i],
    rw ["[", expr hsucc, ",", expr hc i (fin.succ_pos _), ",", expr zero_mul, ",", expr add_zero, "]"] [] },
  set [] [ident M'] [] [":="] [expr update_row M k.succ (N k.succ)] ["with", ident hM'],
  have [ident hM] [":", expr «expr = »(M, update_row M' k.succ «expr + »(M' k.succ, «expr • »(c k, M k.cast_succ)))] [],
  { ext [] [ident i, ident j] [],
    by_cases [expr hi, ":", expr «expr = »(i, k.succ)],
    { simp [] [] [] ["[", expr hi, ",", expr hM', ",", expr hsucc, ",", expr update_row_self, "]"] [] [] },
    rw ["[", expr update_row_ne hi, ",", expr hM', ",", expr update_row_ne hi, "]"] [] },
  have [ident k_ne_succ] [":", expr «expr ≠ »(k.cast_succ, k.succ)] [":=", expr (fin.cast_succ_lt_succ k).ne],
  have [ident M_k] [":", expr «expr = »(M k.cast_succ, M' k.cast_succ)] [":=", expr (update_row_ne k_ne_succ).symm],
  rw ["[", expr hM, ",", expr M_k, ",", expr det_update_row_add_smul_self M' k_ne_succ.symm, ",", expr ih (function.update c k 0), "]"] [],
  { intros [ident i, ident hi],
    rw ["[", expr fin.lt_iff_coe_lt_coe, ",", expr fin.coe_cast_succ, ",", expr fin.coe_succ, ",", expr nat.lt_succ_iff, "]"] ["at", ident hi],
    rw [expr function.update_apply] [],
    split_ifs [] ["with", ident hik],
    { refl },
    exact [expr hc _ (fin.succ_lt_succ_iff.mpr (lt_of_le_of_ne hi (ne.symm hik)))] },
  { rwa ["[", expr hM', ",", expr update_row_ne (fin.succ_ne_zero _).symm, "]"] [] },
  intros [ident i, ident j],
  rw [expr function.update_apply] [],
  split_ifs [] ["with", ident hik],
  { rw ["[", expr zero_mul, ",", expr add_zero, ",", expr hM', ",", expr hik, ",", expr update_row_self, "]"] [] },
  rw ["[", expr hM', ",", expr update_row_ne ((fin.succ_injective _).ne hik), ",", expr hsucc, "]"] [],
  by_cases [expr hik2, ":", expr «expr < »(k, i)],
  { simp [] [] [] ["[", expr hc i (fin.succ_lt_succ_iff.mpr hik2), "]"] [] [] },
  rw [expr update_row_ne] [],
  apply [expr ne_of_lt],
  rwa ["[", expr fin.lt_iff_coe_lt_coe, ",", expr fin.coe_cast_succ, ",", expr fin.coe_succ, ",", expr nat.lt_succ_iff, ",", "<-", expr not_lt, "]"] []
end

/-- If you add multiples of previous rows to the next row, the determinant doesn't change. -/
theorem det_eq_of_forall_row_eq_smul_add_pred {n : ℕ} {A B : Matrix (Finₓ (n+1)) (Finₓ (n+1)) R} (c : Finₓ n → R)
  (A_zero : ∀ j, A 0 j = B 0 j) (A_succ : ∀ (i : Finₓ n) j, A i.succ j = B i.succ j+c i*A i.cast_succ j) :
  det A = det B :=
  det_eq_of_forall_row_eq_smul_add_pred_aux (Finₓ.last _) c (fun i hi => absurd hi (not_lt_of_geₓ (Finₓ.le_last _)))
    A_zero A_succ

/-- If you add multiples of previous columns to the next columns, the determinant doesn't change. -/
theorem det_eq_of_forall_col_eq_smul_add_pred {n : ℕ} {A B : Matrix (Finₓ (n+1)) (Finₓ (n+1)) R} (c : Finₓ n → R)
  (A_zero : ∀ i, A i 0 = B i 0) (A_succ : ∀ i (j : Finₓ n), A i j.succ = B i j.succ+c j*A i j.cast_succ) :
  det A = det B :=
  by 
    rw [←det_transpose A, ←det_transpose B]
    exact det_eq_of_forall_row_eq_smul_add_pred c A_zero fun i j => A_succ j i

end DetEq

-- error in LinearAlgebra.Matrix.Determinant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem det_block_diagonal
{o : Type*}
[fintype o]
[decidable_eq o]
(M : o → matrix n n R) : «expr = »((block_diagonal M).det, «expr∏ , »((k), (M k).det)) :=
begin
  simp_rw ["[", expr det_apply', "]"] [],
  rw [expr finset.prod_sum] [],
  simp_rw ["[", expr finset.mem_univ, ",", expr finset.prod_attach_univ, ",", expr finset.univ_pi_univ, "]"] [],
  let [ident preserving_snd] [":", expr finset (equiv.perm «expr × »(n, o))] [":=", expr finset.univ.filter (λ
    σ, ∀ x, «expr = »((σ x).snd, x.snd))],
  have [ident mem_preserving_snd] [":", expr ∀
   {σ : equiv.perm «expr × »(n, o)}, «expr ↔ »(«expr ∈ »(σ, preserving_snd), ∀
    x, «expr = »((σ x).snd, x.snd))] [":=", expr λ σ, finset.mem_filter.trans ⟨λ h, h.2, λ h, ⟨finset.mem_univ _, h⟩⟩],
  rw ["<-", expr finset.sum_subset (finset.subset_univ preserving_snd) _] [],
  rw [expr (finset.sum_bij (λ
     (σ : ∀ k : o, «expr ∈ »(k, finset.univ) → equiv.perm n)
     (_), prod_congr_left (λ k, σ k (finset.mem_univ k))) _ _ _ _).symm] [],
  { intros [ident σ, "_"],
    rw [expr mem_preserving_snd] [],
    rintros ["⟨", ident k, ",", ident x, "⟩"],
    simp [] [] ["only"] ["[", expr prod_congr_left_apply, "]"] [] [] },
  { intros [ident σ, "_"],
    rw ["[", expr finset.prod_mul_distrib, ",", "<-", expr finset.univ_product_univ, ",", expr finset.prod_product_right, "]"] [],
    simp [] [] ["only"] ["[", expr sign_prod_congr_left, ",", expr units.coe_prod, ",", expr int.cast_prod, ",", expr block_diagonal_apply_eq, ",", expr prod_congr_left_apply, "]"] [] [] },
  { intros [ident σ, ident σ', "_", "_", ident eq],
    ext [] [ident x, ident hx, ident k] [],
    simp [] [] ["only"] [] [] ["at", ident eq],
    have [] [":", expr ∀
     k
     x, «expr = »(prod_congr_left (λ
       k, σ k (finset.mem_univ _)) (k, x), prod_congr_left (λ
       k, σ' k (finset.mem_univ _)) (k, x))] [":=", expr λ k x, by rw [expr eq] []],
    simp [] [] ["only"] ["[", expr prod_congr_left_apply, ",", expr prod.mk.inj_iff, "]"] [] ["at", ident this],
    exact [expr (this k x).1] },
  { intros [ident σ, ident hσ],
    rw [expr mem_preserving_snd] ["at", ident hσ],
    have [ident hσ'] [":", expr ∀ x, «expr = »((«expr ⁻¹»(σ) x).snd, x.snd)] [],
    { intro [ident x],
      conv_rhs [] [] { rw ["[", "<-", expr perm.apply_inv_self σ x, ",", expr hσ, "]"] } },
    have [ident mk_apply_eq] [":", expr ∀ k x, «expr = »(((σ (x, k)).fst, k), σ (x, k))] [],
    { intros [ident k, ident x],
      ext [] [] [],
      { simp [] [] ["only"] [] [] [] },
      { simp [] [] ["only"] ["[", expr hσ, "]"] [] [] } },
    have [ident mk_inv_apply_eq] [":", expr ∀ k x, «expr = »(((«expr ⁻¹»(σ) (x, k)).fst, k), «expr ⁻¹»(σ) (x, k))] [],
    { intros [ident k, ident x],
      conv_lhs [] [] { rw ["<-", expr perm.apply_inv_self σ (x, k)] },
      ext [] [] [],
      { simp [] [] ["only"] ["[", expr apply_inv_self, "]"] [] [] },
      { simp [] [] ["only"] ["[", expr hσ', "]"] [] [] } },
    refine [expr ⟨λ k _, ⟨λ x, (σ (x, k)).fst, λ x, («expr ⁻¹»(σ) (x, k)).fst, _, _⟩, _, _⟩],
    { intro [ident x],
      simp [] [] ["only"] ["[", expr mk_apply_eq, ",", expr inv_apply_self, "]"] [] [] },
    { intro [ident x],
      simp [] [] ["only"] ["[", expr mk_inv_apply_eq, ",", expr apply_inv_self, "]"] [] [] },
    { apply [expr finset.mem_univ] },
    { ext [] ["⟨", ident k, ",", ident x, "⟩"] [],
      { simp [] [] ["only"] ["[", expr coe_fn_mk, ",", expr prod_congr_left_apply, "]"] [] [] },
      { simp [] [] ["only"] ["[", expr prod_congr_left_apply, ",", expr hσ, "]"] [] [] } } },
  { intros [ident σ, "_", ident hσ],
    rw [expr mem_preserving_snd] ["at", ident hσ],
    obtain ["⟨", "⟨", ident k, ",", ident x, "⟩", ",", ident hkx, "⟩", ":=", expr not_forall.mp hσ],
    rw ["[", expr finset.prod_eq_zero (finset.mem_univ (k, x)), ",", expr mul_zero, "]"] [],
    rw ["[", "<-", expr @prod.mk.eta _ _ (σ (k, x)), ",", expr block_diagonal_apply_ne, "]"] [],
    exact [expr hkx] }
end

-- error in LinearAlgebra.Matrix.Determinant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The determinant of a 2x2 block matrix with the lower-left block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`matrix.upper_block_triangular_det`. -/
theorem upper_two_block_triangular_det
(A : matrix m m R)
(B : matrix m n R)
(D : matrix n n R) : «expr = »((matrix.from_blocks A B 0 D).det, «expr * »(A.det, D.det)) :=
begin
  classical,
  simp_rw [expr det_apply'] [],
  convert [] [expr (sum_subset (subset_univ ((sum_congr_hom m n).range : set (perm «expr ⊕ »(m, n))).to_finset) _).symm] [],
  rw [expr sum_mul_sum] [],
  simp_rw [expr univ_product_univ] [],
  rw [expr (sum_bij (λ (σ : «expr × »(perm m, perm n)) (_), equiv.sum_congr σ.fst σ.snd) _ _ _ _).symm] [],
  { intros [ident σ₁₂, ident h],
    simp [] [] ["only"] ["[", "]"] [] [],
    erw ["[", expr set.mem_to_finset, ",", expr monoid_hom.mem_range, "]"] [],
    use [expr σ₁₂],
    simp [] [] ["only"] ["[", expr sum_congr_hom_apply, "]"] [] [] },
  { simp [] [] ["only"] ["[", expr forall_prop_of_true, ",", expr prod.forall, ",", expr mem_univ, "]"] [] [],
    intros [ident σ₁, ident σ₂],
    rw [expr fintype.prod_sum_type] [],
    simp_rw ["[", expr equiv.sum_congr_apply, ",", expr sum.map_inr, ",", expr sum.map_inl, ",", expr from_blocks_apply₁₁, ",", expr from_blocks_apply₂₂, "]"] [],
    have [ident hr] [":", expr ∀
     a
     b
     c
     d : R, «expr = »(«expr * »(«expr * »(a, b), «expr * »(c, d)), «expr * »(«expr * »(a, c), «expr * »(b, d)))] [],
    { intros [],
      ac_refl },
    rw [expr hr] [],
    congr,
    rw ["[", expr sign_sum_congr, ",", expr units.coe_mul, ",", expr int.cast_mul, "]"] [] },
  { intros [ident σ₁, ident σ₂, ident h₁, ident h₂],
    dsimp ["only"] ["[", "]"] [] [],
    intro [ident h],
    have [ident h2] [":", expr ∀ x, «expr = »(perm.sum_congr σ₁.fst σ₁.snd x, perm.sum_congr σ₂.fst σ₂.snd x)] [],
    { intro [ident x],
      exact [expr congr_fun (congr_arg to_fun h) x] },
    simp [] [] ["only"] ["[", expr sum.map_inr, ",", expr sum.map_inl, ",", expr perm.sum_congr_apply, ",", expr sum.forall, "]"] [] ["at", ident h2],
    ext [] [] [],
    { exact [expr h2.left x] },
    { exact [expr h2.right x] } },
  { intros [ident σ, ident hσ],
    erw ["[", expr set.mem_to_finset, ",", expr monoid_hom.mem_range, "]"] ["at", ident hσ],
    obtain ["⟨", ident σ₁₂, ",", ident hσ₁₂, "⟩", ":=", expr hσ],
    use [expr σ₁₂],
    rw ["<-", expr hσ₁₂] [],
    simp [] [] [] [] [] [] },
  { intros [ident σ, ident hσ, ident hσn],
    have [ident h1] [":", expr «expr¬ »(∀ x, «expr∃ , »((y), «expr = »(sum.inl y, σ (sum.inl x))))] [],
    { by_contradiction [],
      rw [expr set.mem_to_finset] ["at", ident hσn],
      apply [expr absurd (mem_sum_congr_hom_range_of_perm_maps_to_inl _) hσn],
      rintros [ident x, "⟨", ident a, ",", ident ha, "⟩"],
      rw ["[", "<-", expr ha, "]"] [],
      exact [expr h a] },
    obtain ["⟨", ident a, ",", ident ha, "⟩", ":=", expr not_forall.mp h1],
    cases [expr hx, ":", expr σ (sum.inl a)] ["with", ident a2, ident b],
    { have [ident hn] [] [":=", expr not_exists.mp ha a2],
      exact [expr absurd hx.symm hn] },
    { rw ["[", expr finset.prod_eq_zero (finset.mem_univ (sum.inl a)), ",", expr mul_zero, "]"] [],
      rw ["[", expr hx, ",", expr from_blocks_apply₂₁, "]"] [],
      refl } }
end

-- error in LinearAlgebra.Matrix.Determinant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column 0. -/
theorem det_succ_column_zero
{n : exprℕ()}
(A : matrix (fin n.succ) (fin n.succ) R) : «expr = »(det A, «expr∑ , »((i : fin n.succ), «expr * »(«expr * »(«expr ^ »(«expr- »(1), (i : exprℕ())), A i 0), det (A.minor i.succ_above fin.succ)))) :=
begin
  rw ["[", expr matrix.det_apply, ",", expr finset.univ_perm_fin_succ, ",", "<-", expr finset.univ_product_univ, "]"] [],
  simp [] [] ["only"] ["[", expr finset.sum_map, ",", expr equiv.to_embedding_apply, ",", expr finset.sum_product, ",", expr matrix.minor, "]"] [] [],
  refine [expr finset.sum_congr rfl (λ i _, fin.cases _ (λ i, _) i)],
  { simp [] [] ["only"] ["[", expr fin.prod_univ_succ, ",", expr matrix.det_apply, ",", expr finset.mul_sum, ",", expr equiv.perm.decompose_fin_symm_apply_zero, ",", expr fin.coe_zero, ",", expr one_mul, ",", expr equiv.perm.decompose_fin.symm_sign, ",", expr equiv.swap_self, ",", expr if_true, ",", expr id.def, ",", expr eq_self_iff_true, ",", expr equiv.perm.decompose_fin_symm_apply_succ, ",", expr fin.succ_above_zero, ",", expr equiv.coe_refl, ",", expr pow_zero, ",", expr mul_smul_comm, "]"] [] [] },
  have [] [":", expr «expr = »(«expr ^ »((«expr- »(1) : R), (i : exprℕ())), i.cycle_range.sign)] [],
  { simp [] [] [] ["[", expr fin.sign_cycle_range, "]"] [] [] },
  rw ["[", expr fin.coe_succ, ",", expr pow_succ, ",", expr this, ",", expr mul_assoc, ",", expr mul_assoc, ",", expr mul_left_comm «expr↑ »(equiv.perm.sign _), ",", "<-", expr det_permute, ",", expr matrix.det_apply, ",", expr finset.mul_sum, ",", expr finset.mul_sum, "]"] [],
  refine [expr finset.sum_congr rfl (λ σ _, _)],
  rw ["[", expr equiv.perm.decompose_fin.symm_sign, ",", expr if_neg (fin.succ_ne_zero i), "]"] [],
  calc
    «expr = »(«expr • »((«expr * »(«expr- »(1), σ.sign) : exprℤ()), «expr∏ , »((i'), A (equiv.perm.decompose_fin.symm (fin.succ i, σ) i') i')), «expr • »((«expr * »(«expr- »(1), σ.sign) : exprℤ()), «expr * »(A (fin.succ i) 0, «expr∏ , »((i'), A ((fin.succ i).succ_above (fin.cycle_range i (σ i'))) i'.succ)))) : by simp [] [] ["only"] ["[", expr fin.prod_univ_succ, ",", expr fin.succ_above_cycle_range, ",", expr equiv.perm.decompose_fin_symm_apply_zero, ",", expr equiv.perm.decompose_fin_symm_apply_succ, "]"] [] []
    «expr = »(..., «expr * »(«expr- »(1), «expr * »(A (fin.succ i) 0, «expr • »((σ.sign : exprℤ()), «expr∏ , »((i'), A ((fin.succ i).succ_above (fin.cycle_range i (σ i'))) i'.succ))))) : by simp [] [] ["only"] ["[", expr mul_assoc, ",", expr mul_comm, ",", expr neg_mul_eq_neg_mul_symm, ",", expr one_mul, ",", expr zsmul_eq_mul, ",", expr neg_inj, ",", expr neg_smul, ",", expr fin.succ_above_cycle_range, "]"] [] []
end

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row 0. -/
theorem det_succ_row_zero {n : ℕ} (A : Matrix (Finₓ n.succ) (Finₓ n.succ) R) :
  det A = ∑j : Finₓ n.succ, ((-1^(j : ℕ))*A 0 j)*det (A.minor Finₓ.succ j.succ_above) :=
  by 
    rw [←det_transpose A, det_succ_column_zero]
    refine' Finset.sum_congr rfl fun i _ => _ 
    rw [←det_transpose]
    simp only [transpose_apply, transpose_minor, transpose_transpose]

-- error in LinearAlgebra.Matrix.Determinant: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row `i`. -/
theorem det_succ_row
{n : exprℕ()}
(A : matrix (fin n.succ) (fin n.succ) R)
(i : fin n.succ) : «expr = »(det A, «expr∑ , »((j : fin n.succ), «expr * »(«expr * »(«expr ^ »(«expr- »(1), («expr + »(i, j) : exprℕ())), A i j), det (A.minor i.succ_above j.succ_above)))) :=
begin
  simp_rw ["[", expr pow_add, ",", expr mul_assoc, ",", "<-", expr mul_sum, "]"] [],
  have [] [":", expr «expr = »(det A, «expr * »(«expr * »(«expr ^ »((«expr- »(1) : R), (i : exprℕ())), «expr ⁻¹»(i.cycle_range).sign), det A))] [],
  { calc
      «expr = »(det A, «expr * »(«expr↑ »((«expr * »(«expr ^ »((«expr- »(1) : units exprℤ()), (i : exprℕ())), «expr ^ »((«expr- »(1) : units exprℤ()), (i : exprℕ()))) : units exprℤ())), det A)) : by simp [] [] [] [] [] []
      «expr = »(..., «expr * »(«expr * »(«expr ^ »((«expr- »(1) : R), (i : exprℕ())), «expr ⁻¹»(i.cycle_range).sign), det A)) : by simp [] [] [] ["[", "-", ident int.units_mul_self, "]"] [] [] },
  rw ["[", expr this, ",", expr mul_assoc, "]"] [],
  congr,
  rw ["[", "<-", expr det_permute, ",", expr det_succ_row_zero, "]"] [],
  refine [expr finset.sum_congr rfl (λ j _, _)],
  rw ["[", expr mul_assoc, ",", expr matrix.minor, ",", expr matrix.minor, "]"] [],
  congr,
  { rw ["[", expr equiv.perm.inv_def, ",", expr fin.cycle_range_symm_zero, "]"] [] },
  { ext [] [ident i', ident j'] [],
    rw ["[", expr equiv.perm.inv_def, ",", expr fin.cycle_range_symm_succ, "]"] [] }
end

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column `j`. -/
theorem det_succ_column {n : ℕ} (A : Matrix (Finₓ n.succ) (Finₓ n.succ) R) (j : Finₓ n.succ) :
  det A = ∑i : Finₓ n.succ, ((-1^(i+j : ℕ))*A i j)*det (A.minor i.succ_above j.succ_above) :=
  by 
    rw [←det_transpose, det_succ_row _ j]
    refine' Finset.sum_congr rfl fun i _ => _ 
    rw [add_commₓ, ←det_transpose, transpose_apply, transpose_minor, transpose_transpose]

/-- Determinant of 0x0 matrix -/
@[simp]
theorem det_fin_zero {A : Matrix (Finₓ 0) (Finₓ 0) R} : det A = 1 :=
  det_is_empty

/-- Determinant of 1x1 matrix -/
theorem det_fin_one (A : Matrix (Finₓ 1) (Finₓ 1) R) : det A = A 0 0 :=
  det_unique A

/-- Determinant of 2x2 matrix -/
theorem det_fin_two (A : Matrix (Finₓ 2) (Finₓ 2) R) : det A = (A 0 0*A 1 1) - A 0 1*A 1 0 :=
  by 
    simp [Matrix.det_succ_row_zero, Finₓ.sum_univ_succ]
    ring

/-- Determinant of 3x3 matrix -/
theorem det_fin_three (A : Matrix (Finₓ 3) (Finₓ 3) R) :
  det A =
    ((((((A 0 0*A 1 1)*A 2 2) - (A 0 0*A 1 2)*A 2 1) - (A 0 1*A 1 0)*A 2 2)+(A 0 1*A 1 2)*A 2 0)+(A 0 2*A 1 0)*A 2 1) -
      (A 0 2*A 1 1)*A 2 0 :=
  by 
    simp [Matrix.det_succ_row_zero, Finₓ.sum_univ_succ]
    ring

end Matrix

