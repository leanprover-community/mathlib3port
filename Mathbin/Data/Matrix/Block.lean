/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin

! This file was ported from Lean 3 source module data.matrix.block
! leanprover-community/mathlib commit 550b58538991c8977703fdeb7c9d51a5aa27df11
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic

/-!
# Block Matrices

## Main definitions

* `matrix.from_blocks`: build a block matrix out of 4 blocks
* `matrix.to_blocks₁₁`, `matrix.to_blocks₁₂`, `matrix.to_blocks₂₁`, `matrix.to_blocks₂₂`:
  extract each of the four blocks from `matrix.from_blocks`.
* `matrix.block_diagonal`: block diagonal of equally sized blocks. On square blocks, this is a
  ring homomorphisms, `matrix.block_diagonal_ring_hom`.
* `matrix.block_diag`: extract the blocks from the diagonal of a block diagonal matrix.
* `matrix.block_diagonal'`: block diagonal of unequally sized blocks. On square blocks, this is a
  ring homomorphisms, `matrix.block_diagonal'_ring_hom`.
* `matrix.block_diag'`: extract the blocks from the diagonal of a block diagonal matrix.
-/


variable {l m n o p q : Type _} {m' n' p' : o → Type _}

variable {R : Type _} {S : Type _} {α : Type _} {β : Type _}

open Matrix

namespace Matrix

section BlockMatrices

/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
@[pp_nodot]
def fromBlocks (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    Matrix (Sum n o) (Sum l m) α :=
  of <| Sum.elim (fun i => Sum.elim (A i) (B i)) fun i => Sum.elim (C i) (D i)
#align matrix.from_blocks Matrix.fromBlocks

@[simp]
theorem from_blocks_apply₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : l) : fromBlocks A B C D (Sum.inl i) (Sum.inl j) = A i j :=
  rfl
#align matrix.from_blocks_apply₁₁ Matrix.from_blocks_apply₁₁

@[simp]
theorem from_blocks_apply₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : m) : fromBlocks A B C D (Sum.inl i) (Sum.inr j) = B i j :=
  rfl
#align matrix.from_blocks_apply₁₂ Matrix.from_blocks_apply₁₂

@[simp]
theorem from_blocks_apply₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : l) : fromBlocks A B C D (Sum.inr i) (Sum.inl j) = C i j :=
  rfl
#align matrix.from_blocks_apply₂₁ Matrix.from_blocks_apply₂₁

@[simp]
theorem from_blocks_apply₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : m) : fromBlocks A B C D (Sum.inr i) (Sum.inr j) = D i j :=
  rfl
#align matrix.from_blocks_apply₂₂ Matrix.from_blocks_apply₂₂

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top left" submatrix. -/
def toBlocks₁₁ (M : Matrix (Sum n o) (Sum l m) α) : Matrix n l α :=
  of fun i j => M (Sum.inl i) (Sum.inl j)
#align matrix.to_blocks₁₁ Matrix.toBlocks₁₁

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top right" submatrix. -/
def toBlocks₁₂ (M : Matrix (Sum n o) (Sum l m) α) : Matrix n m α :=
  of fun i j => M (Sum.inl i) (Sum.inr j)
#align matrix.to_blocks₁₂ Matrix.toBlocks₁₂

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom left" submatrix. -/
def toBlocks₂₁ (M : Matrix (Sum n o) (Sum l m) α) : Matrix o l α :=
  of fun i j => M (Sum.inr i) (Sum.inl j)
#align matrix.to_blocks₂₁ Matrix.toBlocks₂₁

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom right" submatrix. -/
def toBlocks₂₂ (M : Matrix (Sum n o) (Sum l m) α) : Matrix o m α :=
  of fun i j => M (Sum.inr i) (Sum.inr j)
#align matrix.to_blocks₂₂ Matrix.toBlocks₂₂

theorem from_blocks_to_blocks (M : Matrix (Sum n o) (Sum l m) α) :
    fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M := by ext (i j);
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
#align matrix.from_blocks_to_blocks Matrix.from_blocks_to_blocks

@[simp]
theorem to_blocks_from_blocks₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₁ = A :=
  rfl
#align matrix.to_blocks_from_blocks₁₁ Matrix.to_blocks_from_blocks₁₁

@[simp]
theorem to_blocks_from_blocks₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₂ = B :=
  rfl
#align matrix.to_blocks_from_blocks₁₂ Matrix.to_blocks_from_blocks₁₂

@[simp]
theorem to_blocks_from_blocks₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₁ = C :=
  rfl
#align matrix.to_blocks_from_blocks₂₁ Matrix.to_blocks_from_blocks₂₁

@[simp]
theorem to_blocks_from_blocks₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₂ = D :=
  rfl
#align matrix.to_blocks_from_blocks₂₂ Matrix.to_blocks_from_blocks₂₂

theorem from_blocks_map (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
    (f : α → β) : (fromBlocks A B C D).map f = fromBlocks (A.map f) (B.map f) (C.map f) (D.map f) :=
  by ext (i j); rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [from_blocks]
#align matrix.from_blocks_map Matrix.from_blocks_map

theorem from_blocks_transpose (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ := by ext (i j);
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [from_blocks]
#align matrix.from_blocks_transpose Matrix.from_blocks_transpose

theorem from_blocks_conj_transpose [HasStar α] (A : Matrix n l α) (B : Matrix n m α)
    (C : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C D)ᴴ = fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ := by
  simp only [conj_transpose, from_blocks_transpose, from_blocks_map]
#align matrix.from_blocks_conj_transpose Matrix.from_blocks_conj_transpose

@[simp]
theorem from_blocks_submatrix_sum_swap_left (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (f : p → Sum l m) :
    (fromBlocks A B C D).submatrix Sum.swap f = (fromBlocks C D A B).submatrix id f := by
  ext (i j)
  cases i <;> dsimp <;> cases f j <;> rfl
#align matrix.from_blocks_submatrix_sum_swap_left Matrix.from_blocks_submatrix_sum_swap_left

@[simp]
theorem from_blocks_submatrix_sum_swap_right (A : Matrix n l α) (B : Matrix n m α)
    (C : Matrix o l α) (D : Matrix o m α) (f : p → Sum n o) :
    (fromBlocks A B C D).submatrix f Sum.swap = (fromBlocks B A D C).submatrix f id := by
  ext (i j)
  cases j <;> dsimp <;> cases f i <;> rfl
#align matrix.from_blocks_submatrix_sum_swap_right Matrix.from_blocks_submatrix_sum_swap_right

theorem from_blocks_submatrix_sum_swap_sum_swap {l m n o α : Type _} (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).submatrix Sum.swap Sum.swap = fromBlocks D C B A := by simp
#align matrix.from_blocks_submatrix_sum_swap_sum_swap Matrix.from_blocks_submatrix_sum_swap_sum_swap

/-- A 2x2 block matrix is block diagonal if the blocks outside of the diagonal vanish -/
def IsTwoBlockDiagonal [Zero α] (A : Matrix (Sum n o) (Sum l m) α) : Prop :=
  toBlocks₁₂ A = 0 ∧ toBlocks₂₁ A = 0
#align matrix.is_two_block_diagonal Matrix.IsTwoBlockDiagonal

/-- Let `p` pick out certain rows and `q` pick out certain columns of a matrix `M`. Then
  `to_block M p q` is the corresponding block matrix. -/
def toBlock (M : Matrix m n α) (p : m → Prop) (q : n → Prop) : Matrix { a // p a } { a // q a } α :=
  M.submatrix coe coe
#align matrix.to_block Matrix.toBlock

@[simp]
theorem to_block_apply (M : Matrix m n α) (p : m → Prop) (q : n → Prop) (i : { a // p a })
    (j : { a // q a }) : toBlock M p q i j = M ↑i ↑j :=
  rfl
#align matrix.to_block_apply Matrix.to_block_apply

/-- Let `p` pick out certain rows and columns of a square matrix `M`. Then
  `to_square_block_prop M p` is the corresponding block matrix. -/
def toSquareBlockProp (M : Matrix m m α) (p : m → Prop) : Matrix { a // p a } { a // p a } α :=
  toBlock M _ _
#align matrix.to_square_block_prop Matrix.toSquareBlockProp

theorem to_square_block_prop_def (M : Matrix m m α) (p : m → Prop) :
    toSquareBlockProp M p = fun i j => M ↑i ↑j :=
  rfl
#align matrix.to_square_block_prop_def Matrix.to_square_block_prop_def

/-- Let `b` map rows and columns of a square matrix `M` to blocks. Then
  `to_square_block M b k` is the block `k` matrix. -/
def toSquareBlock (M : Matrix m m α) (b : m → β) (k : β) :
    Matrix { a // b a = k } { a // b a = k } α :=
  toSquareBlockProp M _
#align matrix.to_square_block Matrix.toSquareBlock

theorem to_square_block_def (M : Matrix m m α) (b : m → β) (k : β) :
    toSquareBlock M b k = fun i j => M ↑i ↑j :=
  rfl
#align matrix.to_square_block_def Matrix.to_square_block_def

theorem from_blocks_smul [HasSmul R α] (x : R) (A : Matrix n l α) (B : Matrix n m α)
    (C : Matrix o l α) (D : Matrix o m α) :
    x • fromBlocks A B C D = fromBlocks (x • A) (x • B) (x • C) (x • D) := by ext (i j);
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [from_blocks]
#align matrix.from_blocks_smul Matrix.from_blocks_smul

theorem from_blocks_neg [Neg R] (A : Matrix n l R) (B : Matrix n m R) (C : Matrix o l R)
    (D : Matrix o m R) : -fromBlocks A B C D = fromBlocks (-A) (-B) (-C) (-D) := by ext (i j);
  cases i <;> cases j <;> simp [from_blocks]
#align matrix.from_blocks_neg Matrix.from_blocks_neg

theorem from_blocks_add [Add α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (A' : Matrix n l α) (B' : Matrix n m α) (C' : Matrix o l α)
    (D' : Matrix o m α) :
    fromBlocks A B C D + fromBlocks A' B' C' D' = fromBlocks (A + A') (B + B') (C + C') (D + D') :=
  by ext (i j); rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
#align matrix.from_blocks_add Matrix.from_blocks_add

theorem from_blocks_multiply [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (A' : Matrix l p α)
    (B' : Matrix l q α) (C' : Matrix m p α) (D' : Matrix m q α) :
    fromBlocks A B C D ⬝ fromBlocks A' B' C' D' =
      fromBlocks (A ⬝ A' + B ⬝ C') (A ⬝ B' + B ⬝ D') (C ⬝ A' + D ⬝ C') (C ⬝ B' + D ⬝ D') :=
  by ext (i j);
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;>
    simp only [from_blocks, mul_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.add_apply, of_apply]
#align matrix.from_blocks_multiply Matrix.from_blocks_multiply

theorem from_blocks_mul_vec [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : Sum l m → α) :
    mulVec (fromBlocks A B C D) x =
      Sum.elim (mulVec A (x ∘ Sum.inl) + mulVec B (x ∘ Sum.inr))
        (mulVec C (x ∘ Sum.inl) + mulVec D (x ∘ Sum.inr)) :=
  by 
  ext i
  cases i <;> simp [mul_vec, dot_product]
#align matrix.from_blocks_mul_vec Matrix.from_blocks_mul_vec

theorem vec_mul_from_blocks [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : Sum n o → α) :
    vecMul x (fromBlocks A B C D) =
      Sum.elim (vecMul (x ∘ Sum.inl) A + vecMul (x ∘ Sum.inr) C)
        (vecMul (x ∘ Sum.inl) B + vecMul (x ∘ Sum.inr) D) :=
  by 
  ext i
  cases i <;> simp [vec_mul, dot_product]
#align matrix.vec_mul_from_blocks Matrix.vec_mul_from_blocks

variable [DecidableEq l] [DecidableEq m]

section Zero

variable [Zero α]

theorem to_block_diagonal_self (d : m → α) (p : m → Prop) :
    Matrix.toBlock (diagonal d) p p = diagonal fun i : Subtype p => d ↑i := by
  ext (i j)
  by_cases i = j
  · simp [h]
  · simp [One.one, h, fun h' => h <| Subtype.ext h']
#align matrix.to_block_diagonal_self Matrix.to_block_diagonal_self

theorem to_block_diagonal_disjoint (d : m → α) {p q : m → Prop} (hpq : Disjoint p q) :
    Matrix.toBlock (diagonal d) p q = 0 := by
  ext (⟨i, hi⟩⟨j, hj⟩)
  have : i ≠ j := fun heq => hpq.le_bot i ⟨hi, HEq.symm ▸ hj⟩
  simp [diagonal_apply_ne d this]
#align matrix.to_block_diagonal_disjoint Matrix.to_block_diagonal_disjoint

@[simp]
theorem from_blocks_diagonal (d₁ : l → α) (d₂ : m → α) :
    fromBlocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (Sum.elim d₁ d₂) := by ext (i j);
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [diagonal]
#align matrix.from_blocks_diagonal Matrix.from_blocks_diagonal

end Zero

section HasZeroHasOne

variable [Zero α] [One α]

@[simp]
theorem from_blocks_one : fromBlocks (1 : Matrix l l α) 0 0 (1 : Matrix m m α) = 1 := by
  ext (i j)
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [one_apply]
#align matrix.from_blocks_one Matrix.from_blocks_one

@[simp]
theorem to_block_one_self (p : m → Prop) : Matrix.toBlock (1 : Matrix m m α) p p = 1 :=
  to_block_diagonal_self _ p
#align matrix.to_block_one_self Matrix.to_block_one_self

theorem to_block_one_disjoint {p q : m → Prop} (hpq : Disjoint p q) :
    Matrix.toBlock (1 : Matrix m m α) p q = 0 :=
  to_block_diagonal_disjoint _ hpq
#align matrix.to_block_one_disjoint Matrix.to_block_one_disjoint

end HasZeroHasOne

end BlockMatrices

section BlockDiagonal

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/- warning: matrix.block_diagonal -> Matrix.blockDiagonal is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : Zero.{u4} α], (o -> (Matrix.{u1, u2, u4} m n α)) -> (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u4} o] [_inst_2 : Zero.{u1} α], (o -> (Matrix.{u2, u3, u1} m n α)) -> (Matrix.{max u2 u4, max u3 u4, u1} (Prod.{u2, u4} m o) (Prod.{u3, u4} n o) α)
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal Matrix.blockDiagonalₓ'. -/
/-- `matrix.block_diagonal M` turns a homogenously-indexed collection of matrices
`M : o → matrix m n α'` into a `m × o`-by-`n × o` block matrix which has the entries of `M` along
the diagonal and zero elsewhere.

See also `matrix.block_diagonal'` if the matrices may not have the same size everywhere.
-/
def blockDiagonal (M : o → Matrix m n α) : Matrix (m × o) (n × o) α
  | ⟨i, k⟩, ⟨j, k'⟩ => if k = k' then M k i j else 0
#align matrix.block_diagonal Matrix.blockDiagonal

theorem block_diagonal_apply (M : o → Matrix m n α) (ik jk) :
    blockDiagonal M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0 := by
  cases ik
  cases jk
  rfl
#align matrix.block_diagonal_apply Matrix.block_diagonal_apply

@[simp]
theorem block_diagonal_apply_eq (M : o → Matrix m n α) (i j k) :
    blockDiagonal M (i, k) (j, k) = M k i j :=
  if_pos rfl
#align matrix.block_diagonal_apply_eq Matrix.block_diagonal_apply_eq

theorem block_diagonal_apply_ne (M : o → Matrix m n α) (i j) {k k'} (h : k ≠ k') :
    blockDiagonal M (i, k) (j, k') = 0 :=
  if_neg h
#align matrix.block_diagonal_apply_ne Matrix.block_diagonal_apply_ne

theorem block_diagonal_map (M : o → Matrix m n α) (f : α → β) (hf : f 0 = 0) :
    (blockDiagonal M).map f = blockDiagonal fun k => (M k).map f := by
  ext
  simp only [map_apply, block_diagonal_apply, eq_comm]
  rw [apply_ite f, hf]
#align matrix.block_diagonal_map Matrix.block_diagonal_map

@[simp]
theorem block_diagonal_transpose (M : o → Matrix m n α) :
    (blockDiagonal M)ᵀ = blockDiagonal fun k => (M k)ᵀ := by
  ext
  simp only [transpose_apply, block_diagonal_apply, eq_comm]
  split_ifs with h
  · rw [h]
  · rfl
#align matrix.block_diagonal_transpose Matrix.block_diagonal_transpose

@[simp]
theorem block_diagonal_conj_transpose {α : Type _} [AddMonoid α] [StarAddMonoid α]
    (M : o → Matrix m n α) : (blockDiagonal M)ᴴ = blockDiagonal fun k => (M k)ᴴ := by
  simp only [conj_transpose, block_diagonal_transpose]
  rw [block_diagonal_map _ star (star_zero α)]
#align matrix.block_diagonal_conj_transpose Matrix.block_diagonal_conj_transpose

@[simp]
theorem block_diagonal_zero : blockDiagonal (0 : o → Matrix m n α) = 0 := by
  ext
  simp [block_diagonal_apply]
#align matrix.block_diagonal_zero Matrix.block_diagonal_zero

@[simp]
theorem block_diagonal_diagonal [DecidableEq m] (d : o → m → α) :
    (blockDiagonal fun k => diagonal (d k)) = diagonal fun ik => d ik.2 ik.1 := by
  ext (⟨i, k⟩⟨j, k'⟩)
  simp only [block_diagonal_apply, diagonal, Prod.mk.inj_iff, ← ite_and]
  congr 1
  rw [and_comm']
#align matrix.block_diagonal_diagonal Matrix.block_diagonal_diagonal

@[simp]
theorem block_diagonal_one [DecidableEq m] [One α] : blockDiagonal (1 : o → Matrix m m α) = 1 :=
  show (blockDiagonal fun _ : o => diagonal fun _ : m => (1 : α)) = diagonal fun _ => 1 by
    rw [block_diagonal_diagonal]
#align matrix.block_diagonal_one Matrix.block_diagonal_one

end Zero

@[simp]
theorem block_diagonal_add [AddZeroClass α] (M N : o → Matrix m n α) :
    blockDiagonal (M + N) = blockDiagonal M + blockDiagonal N := by
  ext
  simp only [block_diagonal_apply, Pi.add_apply]
  split_ifs <;> simp
#align matrix.block_diagonal_add Matrix.block_diagonal_add

section

variable (o m n α)

/-- `matrix.block_diagonal` as an `add_monoid_hom`. -/
@[simps]
def blockDiagonalAddMonoidHom [AddZeroClass α] :
    (o → Matrix m n α) →+
      Matrix (m × o) (n × o) α where 
  toFun := blockDiagonal
  map_zero' := block_diagonal_zero
  map_add' := block_diagonal_add
#align matrix.block_diagonal_add_monoid_hom Matrix.blockDiagonalAddMonoidHom

end

@[simp]
theorem block_diagonal_neg [AddGroup α] (M : o → Matrix m n α) :
    blockDiagonal (-M) = -blockDiagonal M :=
  map_neg (blockDiagonalAddMonoidHom m n o α) M
#align matrix.block_diagonal_neg Matrix.block_diagonal_neg

@[simp]
theorem block_diagonal_sub [AddGroup α] (M N : o → Matrix m n α) :
    blockDiagonal (M - N) = blockDiagonal M - blockDiagonal N :=
  map_sub (blockDiagonalAddMonoidHom m n o α) M N
#align matrix.block_diagonal_sub Matrix.block_diagonal_sub

@[simp]
theorem block_diagonal_mul [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
    (M : o → Matrix m n α) (N : o → Matrix n p α) :
    (blockDiagonal fun k => M k ⬝ N k) = blockDiagonal M ⬝ blockDiagonal N := by
  ext (⟨i, k⟩⟨j, k'⟩)
  simp only [block_diagonal_apply, mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  split_ifs with h <;> simp [h]
#align matrix.block_diagonal_mul Matrix.block_diagonal_mul

section

variable (α m o)

/-- `matrix.block_diagonal` as a `ring_hom`. -/
@[simps]
def blockDiagonalRingHom [DecidableEq m] [Fintype o] [Fintype m] [NonAssocSemiring α] :
    (o → Matrix m m α) →+* Matrix (m × o) (m × o) α :=
  { blockDiagonalAddMonoidHom m m o α with
    toFun := blockDiagonal
    map_one' := block_diagonal_one
    map_mul' := block_diagonal_mul }
#align matrix.block_diagonal_ring_hom Matrix.blockDiagonalRingHom

end

@[simp]
theorem block_diagonal_pow [DecidableEq m] [Fintype o] [Fintype m] [Semiring α]
    (M : o → Matrix m m α) (n : ℕ) : blockDiagonal (M ^ n) = blockDiagonal M ^ n :=
  map_pow (blockDiagonalRingHom m o α) M n
#align matrix.block_diagonal_pow Matrix.block_diagonal_pow

@[simp]
theorem block_diagonal_smul {R : Type _} [Monoid R] [AddMonoid α] [DistribMulAction R α] (x : R)
    (M : o → Matrix m n α) : blockDiagonal (x • M) = x • blockDiagonal M := by
  ext
  simp only [block_diagonal_apply, Pi.smul_apply]
  split_ifs <;> simp
#align matrix.block_diagonal_smul Matrix.block_diagonal_smul

end BlockDiagonal

section BlockDiag

/- warning: matrix.block_diag -> Matrix.blockDiag is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}}, (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) -> o -> (Matrix.{u1, u2, u4} m n α)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}}, (Matrix.{max u2 u4, max u3 u4, u1} (Prod.{u2, u4} m o) (Prod.{u3, u4} n o) α) -> o -> (Matrix.{u2, u3, u1} m n α)
Case conversion may be inaccurate. Consider using '#align matrix.block_diag Matrix.blockDiagₓ'. -/
/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `matrix.diag`, and the left-inverse of `matrix.block_diagonal`. -/
def blockDiag (M : Matrix (m × o) (n × o) α) (k : o) : Matrix m n α
  | i, j => M (i, k) (j, k)
#align matrix.block_diag Matrix.blockDiag

theorem block_diag_map (M : Matrix (m × o) (n × o) α) (f : α → β) :
    blockDiag (M.map f) = fun k => (blockDiag M k).map f :=
  rfl
#align matrix.block_diag_map Matrix.block_diag_map

@[simp]
theorem block_diag_transpose (M : Matrix (m × o) (n × o) α) (k : o) :
    blockDiag Mᵀ k = (blockDiag M k)ᵀ :=
  ext fun i j => rfl
#align matrix.block_diag_transpose Matrix.block_diag_transpose

@[simp]
theorem block_diag_conj_transpose {α : Type _} [AddMonoid α] [StarAddMonoid α]
    (M : Matrix (m × o) (n × o) α) (k : o) : blockDiag Mᴴ k = (blockDiag M k)ᴴ :=
  ext fun i j => rfl
#align matrix.block_diag_conj_transpose Matrix.block_diag_conj_transpose

section Zero

variable [Zero α] [Zero β]

@[simp]
theorem block_diag_zero : blockDiag (0 : Matrix (m × o) (n × o) α) = 0 :=
  rfl
#align matrix.block_diag_zero Matrix.block_diag_zero

@[simp]
theorem block_diag_diagonal [DecidableEq o] [DecidableEq m] (d : m × o → α) (k : o) :
    blockDiag (diagonal d) k = diagonal fun i => d (i, k) :=
  ext fun i j => by 
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [block_diag, diagonal_apply_eq, diagonal_apply_eq]
    · rw [block_diag, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt _ hij)]
      exact prod.fst_eq_iff.mpr
#align matrix.block_diag_diagonal Matrix.block_diag_diagonal

@[simp]
theorem block_diag_block_diagonal [DecidableEq o] (M : o → Matrix m n α) :
    blockDiag (blockDiagonal M) = M :=
  funext fun k => ext fun i j => block_diagonal_apply_eq _ _ _ _
#align matrix.block_diag_block_diagonal Matrix.block_diag_block_diagonal

@[simp]
theorem block_diag_one [DecidableEq o] [DecidableEq m] [One α] :
    blockDiag (1 : Matrix (m × o) (m × o) α) = 1 :=
  funext <| block_diag_diagonal _
#align matrix.block_diag_one Matrix.block_diag_one

end Zero

@[simp]
theorem block_diag_add [AddZeroClass α] (M N : Matrix (m × o) (n × o) α) :
    blockDiag (M + N) = blockDiag M + blockDiag N :=
  rfl
#align matrix.block_diag_add Matrix.block_diag_add

section

variable (o m n α)

/-- `matrix.block_diag` as an `add_monoid_hom`. -/
@[simps]
def blockDiagAddMonoidHom [AddZeroClass α] :
    Matrix (m × o) (n × o) α →+
      o → Matrix m n α where 
  toFun := blockDiag
  map_zero' := block_diag_zero
  map_add' := block_diag_add
#align matrix.block_diag_add_monoid_hom Matrix.blockDiagAddMonoidHom

end

@[simp]
theorem block_diag_neg [AddGroup α] (M : Matrix (m × o) (n × o) α) :
    blockDiag (-M) = -blockDiag M :=
  map_neg (blockDiagAddMonoidHom m n o α) M
#align matrix.block_diag_neg Matrix.block_diag_neg

@[simp]
theorem block_diag_sub [AddGroup α] (M N : Matrix (m × o) (n × o) α) :
    blockDiag (M - N) = blockDiag M - blockDiag N :=
  map_sub (blockDiagAddMonoidHom m n o α) M N
#align matrix.block_diag_sub Matrix.block_diag_sub

@[simp]
theorem block_diag_smul {R : Type _} [Monoid R] [AddMonoid α] [DistribMulAction R α] (x : R)
    (M : Matrix (m × o) (n × o) α) : blockDiag (x • M) = x • blockDiag M :=
  rfl
#align matrix.block_diag_smul Matrix.block_diag_smul

end BlockDiag

section BlockDiagonal'

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/- warning: matrix.block_diagonal' -> Matrix.blockDiagonal' is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u4} α], (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) -> (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α)
but is expected to have type
  forall {o : Type.{u2}} {m' : o -> Type.{u3}} {n' : o -> Type.{u4}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} o] [_inst_2 : Zero.{u1} α], (forall (i : o), Matrix.{u3, u4, u1} (m' i) (n' i) α) -> (Matrix.{max u2 u3, max u2 u4, u1} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u4} o (fun (i : o) => n' i)) α)
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal' Matrix.blockDiagonal'ₓ'. -/
/-- `matrix.block_diagonal' M` turns `M : Π i, matrix (m i) (n i) α` into a
`Σ i, m i`-by-`Σ i, n i` block matrix which has the entries of `M` along the diagonal
and zero elsewhere.

This is the dependently-typed version of `matrix.block_diagonal`. -/
def blockDiagonal' (M : ∀ i, Matrix (m' i) (n' i) α) : Matrix (Σi, m' i) (Σi, n' i) α
  | ⟨k, i⟩, ⟨k', j⟩ => if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0
#align matrix.block_diagonal' Matrix.blockDiagonal'

theorem block_diagonal'_eq_block_diagonal (M : o → Matrix m n α) {k k'} (i j) :
    blockDiagonal M (i, k) (j, k') = blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ :=
  rfl
#align matrix.block_diagonal'_eq_block_diagonal Matrix.block_diagonal'_eq_block_diagonal

theorem block_diagonal'_submatrix_eq_block_diagonal (M : o → Matrix m n α) :
    (blockDiagonal' M).submatrix (Prod.toSigma ∘ Prod.swap) (Prod.toSigma ∘ Prod.swap) =
      blockDiagonal M :=
  Matrix.ext fun ⟨k, i⟩ ⟨k', j⟩ => rfl
#align
  matrix.block_diagonal'_submatrix_eq_block_diagonal Matrix.block_diagonal'_submatrix_eq_block_diagonal

theorem block_diagonal'_apply (M : ∀ i, Matrix (m' i) (n' i) α) (ik jk) :
    blockDiagonal' M ik jk =
      if h : ik.1 = jk.1 then M ik.1 ik.2 (cast (congr_arg n' h.symm) jk.2) else 0 :=
  by 
  cases ik
  cases jk
  rfl
#align matrix.block_diagonal'_apply Matrix.block_diagonal'_apply

@[simp]
theorem block_diagonal'_apply_eq (M : ∀ i, Matrix (m' i) (n' i) α) (k i j) :
    blockDiagonal' M ⟨k, i⟩ ⟨k, j⟩ = M k i j :=
  dif_pos rfl
#align matrix.block_diagonal'_apply_eq Matrix.block_diagonal'_apply_eq

theorem block_diagonal'_apply_ne (M : ∀ i, Matrix (m' i) (n' i) α) {k k'} (i j) (h : k ≠ k') :
    blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ = 0 :=
  dif_neg h
#align matrix.block_diagonal'_apply_ne Matrix.block_diagonal'_apply_ne

theorem block_diagonal'_map (M : ∀ i, Matrix (m' i) (n' i) α) (f : α → β) (hf : f 0 = 0) :
    (blockDiagonal' M).map f = blockDiagonal' fun k => (M k).map f := by
  ext
  simp only [map_apply, block_diagonal'_apply, eq_comm]
  rw [apply_dite f, hf]
#align matrix.block_diagonal'_map Matrix.block_diagonal'_map

@[simp]
theorem block_diagonal'_transpose (M : ∀ i, Matrix (m' i) (n' i) α) :
    (blockDiagonal' M)ᵀ = blockDiagonal' fun k => (M k)ᵀ := by
  ext (⟨ii, ix⟩⟨ji, jx⟩)
  simp only [transpose_apply, block_diagonal'_apply]
  split_ifs <;> cc
#align matrix.block_diagonal'_transpose Matrix.block_diagonal'_transpose

@[simp]
theorem block_diagonal'_conj_transpose {α} [AddMonoid α] [StarAddMonoid α]
    (M : ∀ i, Matrix (m' i) (n' i) α) : (blockDiagonal' M)ᴴ = blockDiagonal' fun k => (M k)ᴴ := by
  simp only [conj_transpose, block_diagonal'_transpose]
  exact block_diagonal'_map _ star (star_zero α)
#align matrix.block_diagonal'_conj_transpose Matrix.block_diagonal'_conj_transpose

@[simp]
theorem block_diagonal'_zero : blockDiagonal' (0 : ∀ i, Matrix (m' i) (n' i) α) = 0 := by
  ext
  simp [block_diagonal'_apply]
#align matrix.block_diagonal'_zero Matrix.block_diagonal'_zero

@[simp]
theorem block_diagonal'_diagonal [∀ i, DecidableEq (m' i)] (d : ∀ i, m' i → α) :
    (blockDiagonal' fun k => diagonal (d k)) = diagonal fun ik => d ik.1 ik.2 := by
  ext (⟨i, k⟩⟨j, k'⟩)
  simp only [block_diagonal'_apply, diagonal]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp
  · simp [hij]
#align matrix.block_diagonal'_diagonal Matrix.block_diagonal'_diagonal

@[simp]
theorem block_diagonal'_one [∀ i, DecidableEq (m' i)] [One α] :
    blockDiagonal' (1 : ∀ i, Matrix (m' i) (m' i) α) = 1 :=
  show (blockDiagonal' fun i : o => diagonal fun _ : m' i => (1 : α)) = diagonal fun _ => 1 by
    rw [block_diagonal'_diagonal]
#align matrix.block_diagonal'_one Matrix.block_diagonal'_one

end Zero

@[simp]
theorem block_diagonal'_add [AddZeroClass α] (M N : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (M + N) = blockDiagonal' M + blockDiagonal' N := by
  ext
  simp only [block_diagonal'_apply, Pi.add_apply]
  split_ifs <;> simp
#align matrix.block_diagonal'_add Matrix.block_diagonal'_add

section

variable (m' n' α)

/-- `matrix.block_diagonal'` as an `add_monoid_hom`. -/
@[simps]
def blockDiagonal'AddMonoidHom [AddZeroClass α] :
    (∀ i, Matrix (m' i) (n' i) α) →+
      Matrix (Σi, m' i) (Σi, n' i)
        α where 
  toFun := blockDiagonal'
  map_zero' := block_diagonal'_zero
  map_add' := block_diagonal'_add
#align matrix.block_diagonal'_add_monoid_hom Matrix.blockDiagonal'AddMonoidHom

end

@[simp]
theorem block_diagonal'_neg [AddGroup α] (M : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (-M) = -blockDiagonal' M :=
  map_neg (blockDiagonal'AddMonoidHom m' n' α) M
#align matrix.block_diagonal'_neg Matrix.block_diagonal'_neg

@[simp]
theorem block_diagonal'_sub [AddGroup α] (M N : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (M - N) = blockDiagonal' M - blockDiagonal' N :=
  map_sub (blockDiagonal'AddMonoidHom m' n' α) M N
#align matrix.block_diagonal'_sub Matrix.block_diagonal'_sub

@[simp]
theorem block_diagonal'_mul [NonUnitalNonAssocSemiring α] [∀ i, Fintype (n' i)] [Fintype o]
    (M : ∀ i, Matrix (m' i) (n' i) α) (N : ∀ i, Matrix (n' i) (p' i) α) :
    (blockDiagonal' fun k => M k ⬝ N k) = blockDiagonal' M ⬝ blockDiagonal' N := by
  ext (⟨k, i⟩⟨k', j⟩)
  simp only [block_diagonal'_apply, mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · split_ifs <;> simp
  · intro j' hj'
    exact Finset.sum_eq_zero fun _ _ => by rw [dif_neg hj'.symm, zero_mul]
#align matrix.block_diagonal'_mul Matrix.block_diagonal'_mul

section

variable (α m')

/-- `matrix.block_diagonal'` as a `ring_hom`. -/
@[simps]
def blockDiagonal'RingHom [∀ i, DecidableEq (m' i)] [Fintype o] [∀ i, Fintype (m' i)]
    [NonAssocSemiring α] : (∀ i, Matrix (m' i) (m' i) α) →+* Matrix (Σi, m' i) (Σi, m' i) α :=
  { blockDiagonal'AddMonoidHom m' m' α with
    toFun := blockDiagonal'
    map_one' := block_diagonal'_one
    map_mul' := block_diagonal'_mul }
#align matrix.block_diagonal'_ring_hom Matrix.blockDiagonal'RingHom

end

@[simp]
theorem block_diagonal'_pow [∀ i, DecidableEq (m' i)] [Fintype o] [∀ i, Fintype (m' i)] [Semiring α]
    (M : ∀ i, Matrix (m' i) (m' i) α) (n : ℕ) : blockDiagonal' (M ^ n) = blockDiagonal' M ^ n :=
  map_pow (blockDiagonal'RingHom m' α) M n
#align matrix.block_diagonal'_pow Matrix.block_diagonal'_pow

@[simp]
theorem block_diagonal'_smul {R : Type _} [Semiring R] [AddCommMonoid α] [Module R α] (x : R)
    (M : ∀ i, Matrix (m' i) (n' i) α) : blockDiagonal' (x • M) = x • blockDiagonal' M := by
  ext
  simp only [block_diagonal'_apply, Pi.smul_apply]
  split_ifs <;> simp
#align matrix.block_diagonal'_smul Matrix.block_diagonal'_smul

end BlockDiagonal'

section BlockDiag'

/- warning: matrix.block_diag' -> Matrix.blockDiag' is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}}, (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) -> (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α)
but is expected to have type
  forall {o : Type.{u2}} {m' : o -> Type.{u3}} {n' : o -> Type.{u4}} {α : Type.{u1}}, (Matrix.{max u2 u3, max u2 u4, u1} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u4} o (fun (i : o) => n' i)) α) -> (forall (k : o), Matrix.{u3, u4, u1} (m' k) (n' k) α)
Case conversion may be inaccurate. Consider using '#align matrix.block_diag' Matrix.blockDiag'ₓ'. -/
/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `matrix.diag`, and the left-inverse of `matrix.block_diagonal'`. -/
def blockDiag' (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) : Matrix (m' k) (n' k) α
  | i, j => M ⟨k, i⟩ ⟨k, j⟩
#align matrix.block_diag' Matrix.blockDiag'

theorem block_diag'_map (M : Matrix (Σi, m' i) (Σi, n' i) α) (f : α → β) :
    blockDiag' (M.map f) = fun k => (blockDiag' M k).map f :=
  rfl
#align matrix.block_diag'_map Matrix.block_diag'_map

@[simp]
theorem block_diag'_transpose (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) :
    blockDiag' Mᵀ k = (blockDiag' M k)ᵀ :=
  ext fun i j => rfl
#align matrix.block_diag'_transpose Matrix.block_diag'_transpose

@[simp]
theorem block_diag'_conj_transpose {α : Type _} [AddMonoid α] [StarAddMonoid α]
    (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) : blockDiag' Mᴴ k = (blockDiag' M k)ᴴ :=
  ext fun i j => rfl
#align matrix.block_diag'_conj_transpose Matrix.block_diag'_conj_transpose

section Zero

variable [Zero α] [Zero β]

@[simp]
theorem block_diag'_zero : blockDiag' (0 : Matrix (Σi, m' i) (Σi, n' i) α) = 0 :=
  rfl
#align matrix.block_diag'_zero Matrix.block_diag'_zero

@[simp]
theorem block_diag'_diagonal [DecidableEq o] [∀ i, DecidableEq (m' i)] (d : (Σi, m' i) → α)
    (k : o) : blockDiag' (diagonal d) k = diagonal fun i => d ⟨k, i⟩ :=
  ext fun i j => by 
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [block_diag', diagonal_apply_eq, diagonal_apply_eq]
    · rw [block_diag', diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt (fun h => _) hij)]
      cases h
      rfl
#align matrix.block_diag'_diagonal Matrix.block_diag'_diagonal

@[simp]
theorem block_diag'_block_diagonal' [DecidableEq o] (M : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiag' (blockDiagonal' M) = M :=
  funext fun k => ext fun i j => block_diagonal'_apply_eq _ _ _ _
#align matrix.block_diag'_block_diagonal' Matrix.block_diag'_block_diagonal'

@[simp]
theorem block_diag'_one [DecidableEq o] [∀ i, DecidableEq (m' i)] [One α] :
    blockDiag' (1 : Matrix (Σi, m' i) (Σi, m' i) α) = 1 :=
  funext <| block_diag'_diagonal _
#align matrix.block_diag'_one Matrix.block_diag'_one

end Zero

@[simp]
theorem block_diag'_add [AddZeroClass α] (M N : Matrix (Σi, m' i) (Σi, n' i) α) :
    blockDiag' (M + N) = blockDiag' M + blockDiag' N :=
  rfl
#align matrix.block_diag'_add Matrix.block_diag'_add

section

variable (m' n' α)

/-- `matrix.block_diag'` as an `add_monoid_hom`. -/
@[simps]
def blockDiag'AddMonoidHom [AddZeroClass α] :
    Matrix (Σi, m' i) (Σi, n' i) α →+
      ∀ i, Matrix (m' i) (n' i) α where 
  toFun := blockDiag'
  map_zero' := block_diag'_zero
  map_add' := block_diag'_add
#align matrix.block_diag'_add_monoid_hom Matrix.blockDiag'AddMonoidHom

end

@[simp]
theorem block_diag'_neg [AddGroup α] (M : Matrix (Σi, m' i) (Σi, n' i) α) :
    blockDiag' (-M) = -blockDiag' M :=
  map_neg (blockDiag'AddMonoidHom m' n' α) M
#align matrix.block_diag'_neg Matrix.block_diag'_neg

@[simp]
theorem block_diag'_sub [AddGroup α] (M N : Matrix (Σi, m' i) (Σi, n' i) α) :
    blockDiag' (M - N) = blockDiag' M - blockDiag' N :=
  map_sub (blockDiag'AddMonoidHom m' n' α) M N
#align matrix.block_diag'_sub Matrix.block_diag'_sub

@[simp]
theorem block_diag'_smul {R : Type _} [Monoid R] [AddMonoid α] [DistribMulAction R α] (x : R)
    (M : Matrix (Σi, m' i) (Σi, n' i) α) : blockDiag' (x • M) = x • blockDiag' M :=
  rfl
#align matrix.block_diag'_smul Matrix.block_diag'_smul

end BlockDiag'

section

variable [CommRing R]

theorem to_block_mul_eq_mul {m n k : Type _} [Fintype n] (p : m → Prop) (q : k → Prop)
    (A : Matrix m n R) (B : Matrix n k R) : (A ⬝ B).toBlock p q = A.toBlock p ⊤ ⬝ B.toBlock ⊤ q :=
  by 
  ext (i k)
  simp only [to_block_apply, mul_apply]
  rw [Finset.sum_subtype]
  simp [Top.top, CompleteLattice.top, BoundedOrder.top]
#align matrix.to_block_mul_eq_mul Matrix.to_block_mul_eq_mul

theorem to_block_mul_eq_add {m n k : Type _} [Fintype n] (p : m → Prop) (q : n → Prop)
    [DecidablePred q] (r : k → Prop) (A : Matrix m n R) (B : Matrix n k R) :
    (A ⬝ B).toBlock p r =
      A.toBlock p q ⬝ B.toBlock q r + (A.toBlock p fun i => ¬q i) ⬝ B.toBlock (fun i => ¬q i) r :=
  by
  classical 
    ext (i k)
    simp only [to_block_apply, mul_apply, Pi.add_apply]
    convert (Fintype.sum_subtype_add_sum_subtype q fun x => A (↑i) x * B x ↑k).symm
#align matrix.to_block_mul_eq_add Matrix.to_block_mul_eq_add

end

end Matrix

