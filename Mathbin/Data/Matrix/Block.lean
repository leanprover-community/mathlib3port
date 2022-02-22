/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin
-/
import Mathbin.Data.Matrix.Basic

/-!
# Block Matrices

## Main definitions

* `matrix.from_blocks`: build a block matrix out of 4 blocks
* `matrix.to_blocks₁₁`, `matrix.to_blocks₁₂`, `matrix.to_blocks₂₁`, `matrix.to_blocks₂₂`:
  extract each of the four blocks from `matrix.from_blocks`.
* `matrix.block_diagonal`: block diagonal of equally sized blocks
* `matrix.block_diagonal'`: block diagonal of unequally sized blocks
-/


variable {l m n o : Type _} {m' : o → Type _} {n' : o → Type _}

variable {R : Type _} {S : Type _} {α : Type _} {β : Type _}

open_locale Matrix

namespace Matrix

section BlockMatrices

/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
def fromBlocks (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    Matrix (Sum n o) (Sum l m) α :=
  Sum.elim (fun i => Sum.elim (A i) (B i)) fun i => Sum.elim (C i) (D i)

@[simp]
theorem from_blocks_apply₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : n)
    (j : l) : fromBlocks A B C D (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

@[simp]
theorem from_blocks_apply₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : n)
    (j : m) : fromBlocks A B C D (Sum.inl i) (Sum.inr j) = B i j :=
  rfl

@[simp]
theorem from_blocks_apply₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : o)
    (j : l) : fromBlocks A B C D (Sum.inr i) (Sum.inl j) = C i j :=
  rfl

@[simp]
theorem from_blocks_apply₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : o)
    (j : m) : fromBlocks A B C D (Sum.inr i) (Sum.inr j) = D i j :=
  rfl

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top left" submatrix. -/
def toBlocks₁₁ (M : Matrix (Sum n o) (Sum l m) α) : Matrix n l α := fun i j => M (Sum.inl i) (Sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top right" submatrix. -/
def toBlocks₁₂ (M : Matrix (Sum n o) (Sum l m) α) : Matrix n m α := fun i j => M (Sum.inl i) (Sum.inr j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom left" submatrix. -/
def toBlocks₂₁ (M : Matrix (Sum n o) (Sum l m) α) : Matrix o l α := fun i j => M (Sum.inr i) (Sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom right" submatrix. -/
def toBlocks₂₂ (M : Matrix (Sum n o) (Sum l m) α) : Matrix o m α := fun i j => M (Sum.inr i) (Sum.inr j)

theorem from_blocks_to_blocks (M : Matrix (Sum n o) (Sum l m) α) :
    fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

@[simp]
theorem to_blocks_from_blocks₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).toBlocks₁₁ = A :=
  rfl

@[simp]
theorem to_blocks_from_blocks₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).toBlocks₁₂ = B :=
  rfl

@[simp]
theorem to_blocks_from_blocks₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).toBlocks₂₁ = C :=
  rfl

@[simp]
theorem to_blocks_from_blocks₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).toBlocks₂₂ = D :=
  rfl

theorem from_blocks_map (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (f : α → β) :
    (fromBlocks A B C D).map f = fromBlocks (A.map f) (B.map f) (C.map f) (D.map f) := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [from_blocks]

theorem from_blocks_transpose (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D)ᵀ = fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [from_blocks]

theorem from_blocks_conj_transpose [HasStar α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᴴ = fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ := by
  simp only [conj_transpose, from_blocks_transpose, from_blocks_map]

/-- A 2x2 block matrix is block diagonal if the blocks outside of the diagonal vanish -/
def IsTwoBlockDiagonal [Zero α] (A : Matrix (Sum n o) (Sum l m) α) : Prop :=
  toBlocks₁₂ A = 0 ∧ toBlocks₂₁ A = 0

/-- Let `p` pick out certain rows and `q` pick out certain columns of a matrix `M`. Then
  `to_block M p q` is the corresponding block matrix. -/
def toBlock (M : Matrix m n α) (p : m → Prop) (q : n → Prop) : Matrix { a // p a } { a // q a } α :=
  M.minor coe coe

@[simp]
theorem to_block_apply (M : Matrix m n α) (p : m → Prop) (q : n → Prop) (i : { a // p a }) (j : { a // q a }) :
    toBlock M p q i j = M ↑i ↑j :=
  rfl

/-- Let `b` map rows and columns of a square matrix `M` to blocks. Then
  `to_square_block M b k` is the block `k` matrix. -/
def toSquareBlock (M : Matrix m m α) {n : Nat} (b : m → Finₓ n) (k : Finₓ n) :
    Matrix { a // b a = k } { a // b a = k } α :=
  M.minor coe coe

@[simp]
theorem to_square_block_def (M : Matrix m m α) {n : Nat} (b : m → Finₓ n) (k : Finₓ n) :
    toSquareBlock M b k = fun i j => M ↑i ↑j :=
  rfl

/-- Alternate version with `b : m → nat`. Let `b` map rows and columns of a square matrix `M` to
  blocks. Then `to_square_block' M b k` is the block `k` matrix. -/
def toSquareBlock' (M : Matrix m m α) (b : m → Nat) (k : Nat) : Matrix { a // b a = k } { a // b a = k } α :=
  M.minor coe coe

@[simp]
theorem to_square_block_def' (M : Matrix m m α) (b : m → Nat) (k : Nat) : toSquareBlock' M b k = fun i j => M ↑i ↑j :=
  rfl

/-- Let `p` pick out certain rows and columns of a square matrix `M`. Then
  `to_square_block_prop M p` is the corresponding block matrix. -/
def toSquareBlockProp (M : Matrix m m α) (p : m → Prop) : Matrix { a // p a } { a // p a } α :=
  M.minor coe coe

@[simp]
theorem to_square_block_prop_def (M : Matrix m m α) (p : m → Prop) : toSquareBlockProp M p = fun i j => M ↑i ↑j :=
  rfl

variable [Semiringₓ α]

theorem from_blocks_smul (x : α) (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    x • fromBlocks A B C D = fromBlocks (x • A) (x • B) (x • C) (x • D) := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [from_blocks]

theorem from_blocks_add (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (A' : Matrix n l α)
    (B' : Matrix n m α) (C' : Matrix o l α) (D' : Matrix o m α) :
    fromBlocks A B C D + fromBlocks A' B' C' D' = fromBlocks (A + A') (B + B') (C + C') (D + D') := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

theorem from_blocks_multiply {p q : Type _} [Fintype l] [Fintype m] (A : Matrix n l α) (B : Matrix n m α)
    (C : Matrix o l α) (D : Matrix o m α) (A' : Matrix l p α) (B' : Matrix l q α) (C' : Matrix m p α)
    (D' : Matrix m q α) :
    fromBlocks A B C D ⬝ fromBlocks A' B' C' D' =
      fromBlocks (A ⬝ A' + B ⬝ C') (A ⬝ B' + B ⬝ D') (C ⬝ A' + D ⬝ C') (C ⬝ B' + D ⬝ D') :=
  by
  ext i j
  rcases i with ⟨⟩ <;>
    rcases j with ⟨⟩ <;>
      simp only [from_blocks, mul_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply]

variable [DecidableEq l] [DecidableEq m]

@[simp]
theorem from_blocks_diagonal (d₁ : l → α) (d₂ : m → α) :
    fromBlocks (diagonalₓ d₁) 0 0 (diagonalₓ d₂) = diagonalₓ (Sum.elim d₁ d₂) := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [diagonal]

@[simp]
theorem from_blocks_one : fromBlocks (1 : Matrix l l α) 0 0 (1 : Matrix m m α) = 1 := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [one_apply]

end BlockMatrices

section BlockDiagonal

variable (M N : o → Matrix m n α) [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/-- `matrix.block_diagonal M` turns a homogenously-indexed collection of matrices
`M : o → matrix m n α'` into a `m × o`-by-`n × o` block matrix which has the entries of `M` along
the diagonal and zero elsewhere.

See also `matrix.block_diagonal'` if the matrices may not have the same size everywhere.
-/
def blockDiagonal : Matrix (m × o) (n × o) α
  | ⟨i, k⟩, ⟨j, k'⟩ => if k = k' then M k i j else 0

theorem block_diagonal_apply ik jk : blockDiagonal M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0 := by
  cases ik
  cases jk
  rfl

@[simp]
theorem block_diagonal_apply_eq i j k : blockDiagonal M (i, k) (j, k) = M k i j :=
  if_pos rfl

theorem block_diagonal_apply_ne i j {k k'} (h : k ≠ k') : blockDiagonal M (i, k) (j, k') = 0 :=
  if_neg h

theorem block_diagonal_map (f : α → β) (hf : f 0 = 0) : (blockDiagonal M).map f = blockDiagonal fun k => (M k).map f :=
  by
  ext
  simp only [map_apply, block_diagonal_apply, eq_comm]
  rw [apply_ite f, hf]

@[simp]
theorem block_diagonal_transpose : (blockDiagonal M)ᵀ = blockDiagonal fun k => (M k)ᵀ := by
  ext
  simp only [transpose_apply, block_diagonal_apply, eq_comm]
  split_ifs with h
  · rw [h]
    
  · rfl
    

@[simp]
theorem block_diagonal_conj_transpose {α : Type _} [Semiringₓ α] [StarRing α] (M : o → Matrix m n α) :
    (blockDiagonal M)ᴴ = blockDiagonal fun k => (M k)ᴴ := by
  simp only [conj_transpose, block_diagonal_transpose]
  rw [block_diagonal_map _ star (star_zero α)]

@[simp]
theorem block_diagonal_zero : blockDiagonal (0 : o → Matrix m n α) = 0 := by
  ext
  simp [block_diagonal_apply]

@[simp]
theorem block_diagonal_diagonal [DecidableEq m] (d : o → m → α) :
    (blockDiagonal fun k => diagonalₓ (d k)) = diagonalₓ fun ik => d ik.2 ik.1 := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [block_diagonal_apply, diagonal, Prod.mk.inj_iffₓ, ← ite_and]
  congr 1
  rw [and_comm]

@[simp]
theorem block_diagonal_one [DecidableEq m] [One α] : blockDiagonal (1 : o → Matrix m m α) = 1 :=
  show (blockDiagonal fun _ : o => diagonalₓ fun _ : m => (1 : α)) = diagonalₓ fun _ => 1 by
    rw [block_diagonal_diagonal]

end Zero

@[simp]
theorem block_diagonal_add [AddMonoidₓ α] : blockDiagonal (M + N) = blockDiagonal M + blockDiagonal N := by
  ext
  simp only [block_diagonal_apply, Pi.add_apply]
  split_ifs <;> simp

@[simp]
theorem block_diagonal_neg [AddGroupₓ α] : blockDiagonal (-M) = -blockDiagonal M := by
  ext
  simp only [block_diagonal_apply, Pi.neg_apply]
  split_ifs <;> simp

@[simp]
theorem block_diagonal_sub [AddGroupₓ α] : blockDiagonal (M - N) = blockDiagonal M - blockDiagonal N := by
  simp [sub_eq_add_neg]

@[simp]
theorem block_diagonal_mul {p : Type _} [Fintype n] [Fintype o] [Semiringₓ α] (N : o → Matrix n p α) :
    (blockDiagonal fun k => M k ⬝ N k) = blockDiagonal M ⬝ blockDiagonal N := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [block_diagonal_apply, mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  split_ifs with h <;> simp [h]

@[simp]
theorem block_diagonal_smul {R : Type _} [Semiringₓ R] [AddCommMonoidₓ α] [Module R α] (x : R) :
    blockDiagonal (x • M) = x • blockDiagonal M := by
  ext
  simp only [block_diagonal_apply, Pi.smul_apply]
  split_ifs <;> simp

end BlockDiagonal

section BlockDiagonal'

variable (M N : ∀ i, Matrix (m' i) (n' i) α) [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/-- `matrix.block_diagonal' M` turns `M : Π i, matrix (m i) (n i) α` into a
`Σ i, m i`-by-`Σ i, n i` block matrix which has the entries of `M` along the diagonal
and zero elsewhere.

This is the dependently-typed version of `matrix.block_diagonal`. -/
def blockDiagonal' : Matrix (Σi, m' i) (Σi, n' i) α
  | ⟨k, i⟩, ⟨k', j⟩ => if h : k = k' then M k i (cast (congr_argₓ n' h.symm) j) else 0

theorem block_diagonal'_eq_block_diagonal (M : o → Matrix m n α) {k k'} i j :
    blockDiagonal M (i, k) (j, k') = blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ :=
  rfl

theorem block_diagonal'_minor_eq_block_diagonal (M : o → Matrix m n α) :
    (blockDiagonal' M).minor (Prod.toSigma ∘ Prod.swap) (Prod.toSigma ∘ Prod.swap) = blockDiagonal M :=
  Matrix.ext fun ⟨k, i⟩ ⟨k', j⟩ => rfl

theorem block_diagonal'_apply ik jk :
    blockDiagonal' M ik jk = if h : ik.1 = jk.1 then M ik.1 ik.2 (cast (congr_argₓ n' h.symm) jk.2) else 0 := by
  cases ik
  cases jk
  rfl

@[simp]
theorem block_diagonal'_apply_eq k i j : blockDiagonal' M ⟨k, i⟩ ⟨k, j⟩ = M k i j :=
  dif_pos rfl

theorem block_diagonal'_apply_ne {k k'} i j (h : k ≠ k') : blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ = 0 :=
  dif_neg h

theorem block_diagonal'_map (f : α → β) (hf : f 0 = 0) :
    (blockDiagonal' M).map f = blockDiagonal' fun k => (M k).map f := by
  ext
  simp only [map_apply, block_diagonal'_apply, eq_comm]
  rw [apply_dite f, hf]

@[simp]
theorem block_diagonal'_transpose : (blockDiagonal' M)ᵀ = blockDiagonal' fun k => (M k)ᵀ := by
  ext ⟨ii, ix⟩ ⟨ji, jx⟩
  simp only [transpose_apply, block_diagonal'_apply]
  split_ifs <;> cc

@[simp]
theorem block_diagonal'_conj_transpose {α} [Semiringₓ α] [StarRing α] (M : ∀ i, Matrix (m' i) (n' i) α) :
    (blockDiagonal' M)ᴴ = blockDiagonal' fun k => (M k)ᴴ := by
  simp only [conj_transpose, block_diagonal'_transpose]
  exact block_diagonal'_map _ star (star_zero α)

@[simp]
theorem block_diagonal'_zero : blockDiagonal' (0 : ∀ i, Matrix (m' i) (n' i) α) = 0 := by
  ext
  simp [block_diagonal'_apply]

@[simp]
theorem block_diagonal'_diagonal [∀ i, DecidableEq (m' i)] (d : ∀ i, m' i → α) :
    (blockDiagonal' fun k => diagonalₓ (d k)) = diagonalₓ fun ik => d ik.1 ik.2 := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [block_diagonal'_apply, diagonal]
  split_ifs <;> cc

@[simp]
theorem block_diagonal'_one [∀ i, DecidableEq (m' i)] [One α] : blockDiagonal' (1 : ∀ i, Matrix (m' i) (m' i) α) = 1 :=
  show (blockDiagonal' fun i : o => diagonalₓ fun _ : m' i => (1 : α)) = diagonalₓ fun _ => 1 by
    rw [block_diagonal'_diagonal]

end Zero

@[simp]
theorem block_diagonal'_add [AddMonoidₓ α] : blockDiagonal' (M + N) = blockDiagonal' M + blockDiagonal' N := by
  ext
  simp only [block_diagonal'_apply, Pi.add_apply]
  split_ifs <;> simp

@[simp]
theorem block_diagonal'_neg [AddGroupₓ α] : blockDiagonal' (-M) = -blockDiagonal' M := by
  ext
  simp only [block_diagonal'_apply, Pi.neg_apply]
  split_ifs <;> simp

@[simp]
theorem block_diagonal'_sub [AddGroupₓ α] : blockDiagonal' (M - N) = blockDiagonal' M - blockDiagonal' N := by
  simp [sub_eq_add_neg]

@[simp]
theorem block_diagonal'_mul {p : o → Type _} [Semiringₓ α] [∀ i, Fintype (n' i)] [Fintype o]
    (N : ∀ i, Matrix (n' i) (p i) α) : (blockDiagonal' fun k => M k ⬝ N k) = blockDiagonal' M ⬝ blockDiagonal' N := by
  ext ⟨k, i⟩ ⟨k', j⟩
  simp only [block_diagonal'_apply, mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · split_ifs <;> simp
    
  · intro j' hj'
    exact
      Finset.sum_eq_zero fun _ _ => by
        rw [dif_neg hj'.symm, zero_mul]
    

@[simp]
theorem block_diagonal'_smul {R : Type _} [Semiringₓ R] [AddCommMonoidₓ α] [Module R α] (x : R) :
    blockDiagonal' (x • M) = x • blockDiagonal' M := by
  ext
  simp only [block_diagonal'_apply, Pi.smul_apply]
  split_ifs <;> simp

end BlockDiagonal'

end Matrix

