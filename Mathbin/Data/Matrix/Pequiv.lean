import Mathbin.Data.Matrix.Basic 
import Mathbin.Data.Pequiv

/-!
# partial equivalences for matrices

Using partial equivalences to represent matrices.
This file introduces the function `pequiv.to_matrix`, which returns a matrix containing ones and
zeros. For any partial equivalence `f`, `f.to_matrix i j = 1 ↔ f i = some j`.

The following important properties of this function are proved
`to_matrix_trans : (f.trans g).to_matrix = f.to_matrix ⬝ g.to_matrix`
`to_matrix_symm  : f.symm.to_matrix = f.to_matrixᵀ`
`to_matrix_refl : (pequiv.refl n).to_matrix = 1`
`to_matrix_bot : ⊥.to_matrix = 0`

This theory gives the matrix representation of projection linear maps, and their right inverses.
For example, the matrix `(single (0 : fin 1) (i : fin n)).to_matrix` corresponds to the ith
projection map from R^n to R.

Any injective function `fin m → fin n` gives rise to a `pequiv`, whose matrix is the projection
map from R^m → R^n represented by the same function. The transpose of this matrix is the right
inverse of this map, sending anything not in the image to zero.

## notations

This file uses the notation ` ⬝ ` for `matrix.mul` and `ᵀ` for `matrix.transpose`.
-/


namespace Pequiv

open Matrix

universe u v

variable {k l m n : Type _}

variable {α : Type v}

open_locale Matrix

/-- `to_matrix` returns a matrix containing ones and zeros. `f.to_matrix i j` is `1` if
  `f i = some j` and `0` otherwise -/
def to_matrix [DecidableEq n] [HasZero α] [HasOne α] (f : m ≃. n) : Matrix m n α
| i, j => if j ∈ f i then 1 else 0

-- error in Data.Matrix.Pequiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_matrix_apply
[fintype m]
[decidable_eq m]
[semiring α]
(f : «expr ≃. »(l, m))
(M : matrix m n α)
(i j) : «expr = »(«expr ⬝ »(f.to_matrix, M) i j, option.cases_on (f i) 0 (λ fi, M fi j)) :=
begin
  dsimp [] ["[", expr to_matrix, ",", expr matrix.mul_apply, "]"] [] [],
  cases [expr h, ":", expr f i] ["with", ident fi],
  { simp [] [] [] ["[", expr h, "]"] [] [] },
  { rw [expr finset.sum_eq_single fi] []; simp [] [] [] ["[", expr h, ",", expr eq_comm, "]"] [] [] { contextual := tt } }
end

theorem to_matrix_symm [DecidableEq m] [DecidableEq n] [HasZero α] [HasOne α] (f : m ≃. n) :
  (f.symm.to_matrix : Matrix n m α) = (f.to_matrix)ᵀ :=
  by 
    ext <;> simp only [transpose, mem_iff_mem f, to_matrix] <;> congr

@[simp]
theorem to_matrix_refl [DecidableEq n] [HasZero α] [HasOne α] : ((Pequiv.refl n).toMatrix : Matrix n n α) = 1 :=
  by 
    ext <;> simp [to_matrix, one_apply] <;> congr

theorem matrix_mul_apply [Fintype m] [Semiringₓ α] [DecidableEq n] (M : Matrix l m α) (f : m ≃. n) i j :
  (M ⬝ f.to_matrix) i j = Option.casesOn (f.symm j) 0 fun fj => M i fj :=
  by 
    dsimp [to_matrix, Matrix.mul_apply]
    cases' h : f.symm j with fj
    ·
      simp [h, ←f.eq_some_iff]
    ·
      rw [Finset.sum_eq_single fj]
      ·
        simp [h, ←f.eq_some_iff]
      ·
        intro b H n 
        simp [h, ←f.eq_some_iff, n.symm]
      ·
        simp 

theorem to_pequiv_mul_matrix [Fintype m] [DecidableEq m] [Semiringₓ α] (f : m ≃ m) (M : Matrix m n α) :
  f.to_pequiv.to_matrix ⬝ M = fun i => M (f i) :=
  by 
    ext i j 
    rw [mul_matrix_apply, Equiv.to_pequiv_apply]

theorem to_matrix_trans [Fintype m] [DecidableEq m] [DecidableEq n] [Semiringₓ α] (f : l ≃. m) (g : m ≃. n) :
  ((f.trans g).toMatrix : Matrix l n α) = f.to_matrix ⬝ g.to_matrix :=
  by 
    ext i j 
    rw [mul_matrix_apply]
    dsimp [to_matrix, Pequiv.trans]
    cases f i <;> simp 

@[simp]
theorem to_matrix_bot [DecidableEq n] [HasZero α] [HasOne α] : ((⊥ : Pequiv m n).toMatrix : Matrix m n α) = 0 :=
  rfl

theorem to_matrix_injective [DecidableEq n] [MonoidWithZeroₓ α] [Nontrivial α] :
  Function.Injective (@to_matrix m n α _ _ _) :=
  by 
    classical 
    intro f g 
    refine' not_imp_not.1 _ 
    simp only [matrix.ext_iff.symm, to_matrix, Pequiv.ext_iff, not_forall, exists_imp_distrib]
    intro i hi 
    use i 
    cases' hf : f i with fi
    ·
      cases' hg : g i with gi
      ·
        cc
      ·
        use gi 
        simp 
    ·
      use fi 
      simp [hf.symm, Ne.symm hi]

theorem to_matrix_swap [DecidableEq n] [Ringₓ α] (i j : n) :
  (Equiv.swap i j).toPequiv.toMatrix =
    (((1 : Matrix n n α) - (single i i).toMatrix -
          (single j j).toMatrix)+(single i j).toMatrix)+(single j i).toMatrix :=
  by 
    ext 
    dsimp [to_matrix, single, Equiv.swap_apply_def, Equiv.toPequiv, one_apply]
    splitIfs <;> simp_all 

@[simp]
theorem single_mul_single [Fintype n] [DecidableEq k] [DecidableEq m] [DecidableEq n] [Semiringₓ α] (a : m) (b : n)
  (c : k) : ((single a b).toMatrix : Matrix _ _ α) ⬝ (single b c).toMatrix = (single a c).toMatrix :=
  by 
    rw [←to_matrix_trans, single_trans_single]

theorem single_mul_single_of_ne [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] [Semiringₓ α] {b₁ b₂ : n}
  (hb : b₁ ≠ b₂) (a : m) (c : k) : ((single a b₁).toMatrix : Matrix _ _ α) ⬝ (single b₂ c).toMatrix = 0 :=
  by 
    rw [←to_matrix_trans, single_trans_single_of_ne hb, to_matrix_bot]

/-- Restatement of `single_mul_single`, which will simplify expressions in `simp` normal form,
  when associativity may otherwise need to be carefully applied. -/
@[simp]
theorem single_mul_single_right [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] [DecidableEq m] [Semiringₓ α]
  (a : m) (b : n) (c : k) (M : Matrix k l α) :
  (single a b).toMatrix ⬝ ((single b c).toMatrix ⬝ M) = (single a c).toMatrix ⬝ M :=
  by 
    rw [←Matrix.mul_assoc, single_mul_single]

/-- We can also define permutation matrices by permuting the rows of the identity matrix. -/
theorem equiv_to_pequiv_to_matrix [DecidableEq n] [HasZero α] [HasOne α] (σ : Equiv n n) (i j : n) :
  σ.to_pequiv.to_matrix i j = (1 : Matrix n n α) (σ i) j :=
  if_congr Option.some_inj rfl rfl

end Pequiv

