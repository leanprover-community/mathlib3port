/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin

! This file was ported from Lean 3 source module data.matrix.block
! leanprover-community/mathlib commit c060baa79af5ca092c54b8bf04f0f10592f59489
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic

/-!
# Block Matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

open BigOperators Matrix

namespace Matrix

/- warning: matrix.dot_product_block -> Matrix.dotProduct_block is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : Fintype.{u1} m] [_inst_2 : Fintype.{u2} n] [_inst_3 : Mul.{u3} α] [_inst_4 : AddCommMonoid.{u3} α] (v : (Sum.{u1, u2} m n) -> α) (w : (Sum.{u1, u2} m n) -> α), Eq.{succ u3} α (Matrix.dotProduct.{u3, max u1 u2} (Sum.{u1, u2} m n) α (Sum.fintype.{u1, u2} m n _inst_1 _inst_2) _inst_3 _inst_4 v w) (HAdd.hAdd.{u3, u3, u3} α α α (instHAdd.{u3} α (AddZeroClass.toHasAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_4)))) (Matrix.dotProduct.{u3, u1} m α _inst_1 _inst_3 _inst_4 (Function.comp.{succ u1, max (succ u1) (succ u2), succ u3} m (Sum.{u1, u2} m n) α v (Sum.inl.{u1, u2} m n)) (Function.comp.{succ u1, max (succ u1) (succ u2), succ u3} m (Sum.{u1, u2} m n) α w (Sum.inl.{u1, u2} m n))) (Matrix.dotProduct.{u3, u2} n α _inst_2 _inst_3 _inst_4 (Function.comp.{succ u2, max (succ u1) (succ u2), succ u3} n (Sum.{u1, u2} m n) α v (Sum.inr.{u1, u2} m n)) (Function.comp.{succ u2, max (succ u1) (succ u2), succ u3} n (Sum.{u1, u2} m n) α w (Sum.inr.{u1, u2} m n))))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u3} m] [_inst_2 : Fintype.{u2} n] [_inst_3 : Mul.{u1} α] [_inst_4 : AddCommMonoid.{u1} α] (v : (Sum.{u3, u2} m n) -> α) (w : (Sum.{u3, u2} m n) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, max u3 u2} (Sum.{u3, u2} m n) α (instFintypeSum.{u3, u2} m n _inst_1 _inst_2) _inst_3 _inst_4 v w) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_4)))) (Matrix.dotProduct.{u1, u3} m α _inst_1 _inst_3 _inst_4 (Function.comp.{succ u3, max (succ u3) (succ u2), succ u1} m (Sum.{u3, u2} m n) α v (Sum.inl.{u3, u2} m n)) (Function.comp.{succ u3, max (succ u3) (succ u2), succ u1} m (Sum.{u3, u2} m n) α w (Sum.inl.{u3, u2} m n))) (Matrix.dotProduct.{u1, u2} n α _inst_2 _inst_3 _inst_4 (Function.comp.{succ u2, max (succ u3) (succ u2), succ u1} n (Sum.{u3, u2} m n) α v (Sum.inr.{u3, u2} m n)) (Function.comp.{succ u2, max (succ u3) (succ u2), succ u1} n (Sum.{u3, u2} m n) α w (Sum.inr.{u3, u2} m n))))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_block Matrix.dotProduct_blockₓ'. -/
theorem dotProduct_block [Fintype m] [Fintype n] [Mul α] [AddCommMonoid α] (v w : Sum m n → α) :
    v ⬝ᵥ w = v ∘ Sum.inl ⬝ᵥ w ∘ Sum.inl + v ∘ Sum.inr ⬝ᵥ w ∘ Sum.inr :=
  Fintype.sum_sum_type _
#align matrix.dot_product_block Matrix.dotProduct_block

section BlockMatrices

#print Matrix.fromBlocks /-
/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
@[pp_nodot]
def fromBlocks (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    Matrix (Sum n o) (Sum l m) α :=
  of <| Sum.elim (fun i => Sum.elim (A i) (B i)) fun i => Sum.elim (C i) (D i)
#align matrix.from_blocks Matrix.fromBlocks
-/

/- warning: matrix.from_blocks_apply₁₁ -> Matrix.fromBlocks_apply₁₁ is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α) (i : n) (j : l), Eq.{succ u5} α (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D (Sum.inl.{u3, u4} n o i) (Sum.inl.{u1, u2} l m j)) (A i j)
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u2}} {n : Type.{u5}} {o : Type.{u1}} {α : Type.{u3}} (A : Matrix.{u5, u4, u3} n l α) (B : Matrix.{u5, u2, u3} n m α) (C : Matrix.{u1, u4, u3} o l α) (D : Matrix.{u1, u2, u3} o m α) (i : n) (j : l), Eq.{succ u3} α (Matrix.fromBlocks.{u4, u2, u5, u1, u3} l m n o α A B C D (Sum.inl.{u5, u1} n o i) (Sum.inl.{u4, u2} l m j)) (A i j)
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_apply₁₁ Matrix.fromBlocks_apply₁₁ₓ'. -/
@[simp]
theorem fromBlocks_apply₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : l) : fromBlocks A B C D (Sum.inl i) (Sum.inl j) = A i j :=
  rfl
#align matrix.from_blocks_apply₁₁ Matrix.fromBlocks_apply₁₁

/- warning: matrix.from_blocks_apply₁₂ -> Matrix.fromBlocks_apply₁₂ is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α) (i : n) (j : m), Eq.{succ u5} α (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D (Sum.inl.{u3, u4} n o i) (Sum.inr.{u1, u2} l m j)) (B i j)
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u2}} {n : Type.{u5}} {o : Type.{u1}} {α : Type.{u3}} (A : Matrix.{u5, u4, u3} n l α) (B : Matrix.{u5, u2, u3} n m α) (C : Matrix.{u1, u4, u3} o l α) (D : Matrix.{u1, u2, u3} o m α) (i : n) (j : m), Eq.{succ u3} α (Matrix.fromBlocks.{u4, u2, u5, u1, u3} l m n o α A B C D (Sum.inl.{u5, u1} n o i) (Sum.inr.{u4, u2} l m j)) (B i j)
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_apply₁₂ Matrix.fromBlocks_apply₁₂ₓ'. -/
@[simp]
theorem fromBlocks_apply₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : m) : fromBlocks A B C D (Sum.inl i) (Sum.inr j) = B i j :=
  rfl
#align matrix.from_blocks_apply₁₂ Matrix.fromBlocks_apply₁₂

/- warning: matrix.from_blocks_apply₂₁ -> Matrix.fromBlocks_apply₂₁ is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α) (i : o) (j : l), Eq.{succ u5} α (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D (Sum.inr.{u3, u4} n o i) (Sum.inl.{u1, u2} l m j)) (C i j)
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u2}} {n : Type.{u5}} {o : Type.{u1}} {α : Type.{u3}} (A : Matrix.{u5, u4, u3} n l α) (B : Matrix.{u5, u2, u3} n m α) (C : Matrix.{u1, u4, u3} o l α) (D : Matrix.{u1, u2, u3} o m α) (i : o) (j : l), Eq.{succ u3} α (Matrix.fromBlocks.{u4, u2, u5, u1, u3} l m n o α A B C D (Sum.inr.{u5, u1} n o i) (Sum.inl.{u4, u2} l m j)) (C i j)
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_apply₂₁ Matrix.fromBlocks_apply₂₁ₓ'. -/
@[simp]
theorem fromBlocks_apply₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : l) : fromBlocks A B C D (Sum.inr i) (Sum.inl j) = C i j :=
  rfl
#align matrix.from_blocks_apply₂₁ Matrix.fromBlocks_apply₂₁

/- warning: matrix.from_blocks_apply₂₂ -> Matrix.fromBlocks_apply₂₂ is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α) (i : o) (j : m), Eq.{succ u5} α (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D (Sum.inr.{u3, u4} n o i) (Sum.inr.{u1, u2} l m j)) (D i j)
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u2}} {n : Type.{u5}} {o : Type.{u1}} {α : Type.{u3}} (A : Matrix.{u5, u4, u3} n l α) (B : Matrix.{u5, u2, u3} n m α) (C : Matrix.{u1, u4, u3} o l α) (D : Matrix.{u1, u2, u3} o m α) (i : o) (j : m), Eq.{succ u3} α (Matrix.fromBlocks.{u4, u2, u5, u1, u3} l m n o α A B C D (Sum.inr.{u5, u1} n o i) (Sum.inr.{u4, u2} l m j)) (D i j)
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_apply₂₂ Matrix.fromBlocks_apply₂₂ₓ'. -/
@[simp]
theorem fromBlocks_apply₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : m) : fromBlocks A B C D (Sum.inr i) (Sum.inr j) = D i j :=
  rfl
#align matrix.from_blocks_apply₂₂ Matrix.fromBlocks_apply₂₂

#print Matrix.toBlocks₁₁ /-
/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top left" submatrix. -/
def toBlocks₁₁ (M : Matrix (Sum n o) (Sum l m) α) : Matrix n l α :=
  of fun i j => M (Sum.inl i) (Sum.inl j)
#align matrix.to_blocks₁₁ Matrix.toBlocks₁₁
-/

#print Matrix.toBlocks₁₂ /-
/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top right" submatrix. -/
def toBlocks₁₂ (M : Matrix (Sum n o) (Sum l m) α) : Matrix n m α :=
  of fun i j => M (Sum.inl i) (Sum.inr j)
#align matrix.to_blocks₁₂ Matrix.toBlocks₁₂
-/

#print Matrix.toBlocks₂₁ /-
/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom left" submatrix. -/
def toBlocks₂₁ (M : Matrix (Sum n o) (Sum l m) α) : Matrix o l α :=
  of fun i j => M (Sum.inr i) (Sum.inl j)
#align matrix.to_blocks₂₁ Matrix.toBlocks₂₁
-/

#print Matrix.toBlocks₂₂ /-
/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom right" submatrix. -/
def toBlocks₂₂ (M : Matrix (Sum n o) (Sum l m) α) : Matrix o m α :=
  of fun i j => M (Sum.inr i) (Sum.inr j)
#align matrix.to_blocks₂₂ Matrix.toBlocks₂₂
-/

/- warning: matrix.from_blocks_to_blocks -> Matrix.fromBlocks_toBlocks is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} (M : Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α), Eq.{succ (max (max u3 u4) (max u1 u2) u5)} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α (Matrix.toBlocks₁₁.{u1, u2, u3, u4, u5} l m n o α M) (Matrix.toBlocks₁₂.{u1, u2, u3, u4, u5} l m n o α M) (Matrix.toBlocks₂₁.{u1, u2, u3, u4, u5} l m n o α M) (Matrix.toBlocks₂₂.{u1, u2, u3, u4, u5} l m n o α M)) M
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} (M : Matrix.{max u5 u4, max u3 u2, u1} (Sum.{u4, u5} n o) (Sum.{u2, u3} l m) α), Eq.{max (max (max (max (succ u2) (succ u3)) (succ u4)) (succ u5)) (succ u1)} (Matrix.{max u5 u4, max u3 u2, u1} (Sum.{u4, u5} n o) (Sum.{u2, u3} l m) α) (Matrix.fromBlocks.{u2, u3, u4, u5, u1} l m n o α (Matrix.toBlocks₁₁.{u2, u3, u4, u5, u1} l m n o α M) (Matrix.toBlocks₁₂.{u2, u3, u4, u5, u1} l m n o α M) (Matrix.toBlocks₂₁.{u2, u3, u4, u5, u1} l m n o α M) (Matrix.toBlocks₂₂.{u2, u3, u4, u5, u1} l m n o α M)) M
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_to_blocks Matrix.fromBlocks_toBlocksₓ'. -/
theorem fromBlocks_toBlocks (M : Matrix (Sum n o) (Sum l m) α) :
    fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M := by ext (i j);
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
#align matrix.from_blocks_to_blocks Matrix.fromBlocks_toBlocks

/- warning: matrix.to_blocks_from_blocks₁₁ -> Matrix.toBlocks_fromBlocks₁₁ is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α), Eq.{succ (max u3 u1 u5)} (Matrix.{u3, u1, u5} n l α) (Matrix.toBlocks₁₁.{u1, u2, u3, u4, u5} l m n o α (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D)) A
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u2}} {n : Type.{u5}} {o : Type.{u1}} {α : Type.{u3}} (A : Matrix.{u5, u4, u3} n l α) (B : Matrix.{u5, u2, u3} n m α) (C : Matrix.{u1, u4, u3} o l α) (D : Matrix.{u1, u2, u3} o m α), Eq.{max (max (succ u4) (succ u5)) (succ u3)} (Matrix.{u5, u4, u3} n l α) (Matrix.toBlocks₁₁.{u4, u2, u5, u1, u3} l m n o α (Matrix.fromBlocks.{u4, u2, u5, u1, u3} l m n o α A B C D)) A
Case conversion may be inaccurate. Consider using '#align matrix.to_blocks_from_blocks₁₁ Matrix.toBlocks_fromBlocks₁₁ₓ'. -/
@[simp]
theorem toBlocks_fromBlocks₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₁ = A :=
  rfl
#align matrix.to_blocks_from_blocks₁₁ Matrix.toBlocks_fromBlocks₁₁

/- warning: matrix.to_blocks_from_blocks₁₂ -> Matrix.toBlocks_fromBlocks₁₂ is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α), Eq.{succ (max u3 u2 u5)} (Matrix.{u3, u2, u5} n m α) (Matrix.toBlocks₁₂.{u1, u2, u3, u4, u5} l m n o α (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D)) B
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u2}} {n : Type.{u5}} {o : Type.{u1}} {α : Type.{u3}} (A : Matrix.{u5, u4, u3} n l α) (B : Matrix.{u5, u2, u3} n m α) (C : Matrix.{u1, u4, u3} o l α) (D : Matrix.{u1, u2, u3} o m α), Eq.{max (max (succ u2) (succ u5)) (succ u3)} (Matrix.{u5, u2, u3} n m α) (Matrix.toBlocks₁₂.{u4, u2, u5, u1, u3} l m n o α (Matrix.fromBlocks.{u4, u2, u5, u1, u3} l m n o α A B C D)) B
Case conversion may be inaccurate. Consider using '#align matrix.to_blocks_from_blocks₁₂ Matrix.toBlocks_fromBlocks₁₂ₓ'. -/
@[simp]
theorem toBlocks_fromBlocks₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₂ = B :=
  rfl
#align matrix.to_blocks_from_blocks₁₂ Matrix.toBlocks_fromBlocks₁₂

/- warning: matrix.to_blocks_from_blocks₂₁ -> Matrix.toBlocks_fromBlocks₂₁ is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α), Eq.{succ (max u4 u1 u5)} (Matrix.{u4, u1, u5} o l α) (Matrix.toBlocks₂₁.{u1, u2, u3, u4, u5} l m n o α (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D)) C
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u2}} {n : Type.{u5}} {o : Type.{u1}} {α : Type.{u3}} (A : Matrix.{u5, u4, u3} n l α) (B : Matrix.{u5, u2, u3} n m α) (C : Matrix.{u1, u4, u3} o l α) (D : Matrix.{u1, u2, u3} o m α), Eq.{max (max (succ u4) (succ u1)) (succ u3)} (Matrix.{u1, u4, u3} o l α) (Matrix.toBlocks₂₁.{u4, u2, u5, u1, u3} l m n o α (Matrix.fromBlocks.{u4, u2, u5, u1, u3} l m n o α A B C D)) C
Case conversion may be inaccurate. Consider using '#align matrix.to_blocks_from_blocks₂₁ Matrix.toBlocks_fromBlocks₂₁ₓ'. -/
@[simp]
theorem toBlocks_fromBlocks₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₁ = C :=
  rfl
#align matrix.to_blocks_from_blocks₂₁ Matrix.toBlocks_fromBlocks₂₁

/- warning: matrix.to_blocks_from_blocks₂₂ -> Matrix.toBlocks_fromBlocks₂₂ is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α), Eq.{succ (max u4 u2 u5)} (Matrix.{u4, u2, u5} o m α) (Matrix.toBlocks₂₂.{u1, u2, u3, u4, u5} l m n o α (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D)) D
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u2}} {n : Type.{u5}} {o : Type.{u1}} {α : Type.{u3}} (A : Matrix.{u5, u4, u3} n l α) (B : Matrix.{u5, u2, u3} n m α) (C : Matrix.{u1, u4, u3} o l α) (D : Matrix.{u1, u2, u3} o m α), Eq.{max (max (succ u2) (succ u1)) (succ u3)} (Matrix.{u1, u2, u3} o m α) (Matrix.toBlocks₂₂.{u4, u2, u5, u1, u3} l m n o α (Matrix.fromBlocks.{u4, u2, u5, u1, u3} l m n o α A B C D)) D
Case conversion may be inaccurate. Consider using '#align matrix.to_blocks_from_blocks₂₂ Matrix.toBlocks_fromBlocks₂₂ₓ'. -/
@[simp]
theorem toBlocks_fromBlocks₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₂ = D :=
  rfl
#align matrix.to_blocks_from_blocks₂₂ Matrix.toBlocks_fromBlocks₂₂

/- warning: matrix.ext_iff_blocks -> Matrix.ext_iff_blocks is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} {A : Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α} {B : Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α}, Iff (Eq.{succ (max (max u3 u4) (max u1 u2) u5)} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) A B) (And (Eq.{succ (max u3 u1 u5)} (Matrix.{u3, u1, u5} n l α) (Matrix.toBlocks₁₁.{u1, u2, u3, u4, u5} l m n o α A) (Matrix.toBlocks₁₁.{u1, u2, u3, u4, u5} l m n o α B)) (And (Eq.{succ (max u3 u2 u5)} (Matrix.{u3, u2, u5} n m α) (Matrix.toBlocks₁₂.{u1, u2, u3, u4, u5} l m n o α A) (Matrix.toBlocks₁₂.{u1, u2, u3, u4, u5} l m n o α B)) (And (Eq.{succ (max u4 u1 u5)} (Matrix.{u4, u1, u5} o l α) (Matrix.toBlocks₂₁.{u1, u2, u3, u4, u5} l m n o α A) (Matrix.toBlocks₂₁.{u1, u2, u3, u4, u5} l m n o α B)) (Eq.{succ (max u4 u2 u5)} (Matrix.{u4, u2, u5} o m α) (Matrix.toBlocks₂₂.{u1, u2, u3, u4, u5} l m n o α A) (Matrix.toBlocks₂₂.{u1, u2, u3, u4, u5} l m n o α B)))))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} {A : Matrix.{max u5 u4, max u3 u2, u1} (Sum.{u4, u5} n o) (Sum.{u2, u3} l m) α} {B : Matrix.{max u5 u4, max u3 u2, u1} (Sum.{u4, u5} n o) (Sum.{u2, u3} l m) α}, Iff (Eq.{max (max (max (max (succ u2) (succ u3)) (succ u4)) (succ u5)) (succ u1)} (Matrix.{max u5 u4, max u3 u2, u1} (Sum.{u4, u5} n o) (Sum.{u2, u3} l m) α) A B) (And (Eq.{max (max (succ u2) (succ u4)) (succ u1)} (Matrix.{u4, u2, u1} n l α) (Matrix.toBlocks₁₁.{u2, u3, u4, u5, u1} l m n o α A) (Matrix.toBlocks₁₁.{u2, u3, u4, u5, u1} l m n o α B)) (And (Eq.{max (max (succ u3) (succ u4)) (succ u1)} (Matrix.{u4, u3, u1} n m α) (Matrix.toBlocks₁₂.{u2, u3, u4, u5, u1} l m n o α A) (Matrix.toBlocks₁₂.{u2, u3, u4, u5, u1} l m n o α B)) (And (Eq.{max (max (succ u2) (succ u5)) (succ u1)} (Matrix.{u5, u2, u1} o l α) (Matrix.toBlocks₂₁.{u2, u3, u4, u5, u1} l m n o α A) (Matrix.toBlocks₂₁.{u2, u3, u4, u5, u1} l m n o α B)) (Eq.{max (max (succ u3) (succ u5)) (succ u1)} (Matrix.{u5, u3, u1} o m α) (Matrix.toBlocks₂₂.{u2, u3, u4, u5, u1} l m n o α A) (Matrix.toBlocks₂₂.{u2, u3, u4, u5, u1} l m n o α B)))))
Case conversion may be inaccurate. Consider using '#align matrix.ext_iff_blocks Matrix.ext_iff_blocksₓ'. -/
/-- Two block matrices are equal if their blocks are equal. -/
theorem ext_iff_blocks {A B : Matrix (Sum n o) (Sum l m) α} :
    A = B ↔
      A.toBlocks₁₁ = B.toBlocks₁₁ ∧
        A.toBlocks₁₂ = B.toBlocks₁₂ ∧ A.toBlocks₂₁ = B.toBlocks₂₁ ∧ A.toBlocks₂₂ = B.toBlocks₂₂ :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩, fun ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ => by
    rw [← from_blocks_to_blocks A, ← from_blocks_to_blocks B, h₁₁, h₁₂, h₂₁, h₂₂]⟩
#align matrix.ext_iff_blocks Matrix.ext_iff_blocks

/- warning: matrix.from_blocks_inj -> Matrix.fromBlocks_inj is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} {A : Matrix.{u3, u1, u5} n l α} {B : Matrix.{u3, u2, u5} n m α} {C : Matrix.{u4, u1, u5} o l α} {D : Matrix.{u4, u2, u5} o m α} {A' : Matrix.{u3, u1, u5} n l α} {B' : Matrix.{u3, u2, u5} n m α} {C' : Matrix.{u4, u1, u5} o l α} {D' : Matrix.{u4, u2, u5} o m α}, Iff (Eq.{succ (max (max u3 u4) (max u1 u2) u5)} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D) (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A' B' C' D')) (And (Eq.{succ (max u3 u1 u5)} (Matrix.{u3, u1, u5} n l α) A A') (And (Eq.{succ (max u3 u2 u5)} (Matrix.{u3, u2, u5} n m α) B B') (And (Eq.{succ (max u4 u1 u5)} (Matrix.{u4, u1, u5} o l α) C C') (Eq.{succ (max u4 u2 u5)} (Matrix.{u4, u2, u5} o m α) D D'))))
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u2}} {n : Type.{u5}} {o : Type.{u1}} {α : Type.{u3}} {A : Matrix.{u5, u4, u3} n l α} {B : Matrix.{u5, u2, u3} n m α} {C : Matrix.{u1, u4, u3} o l α} {D : Matrix.{u1, u2, u3} o m α} {A' : Matrix.{u5, u4, u3} n l α} {B' : Matrix.{u5, u2, u3} n m α} {C' : Matrix.{u1, u4, u3} o l α} {D' : Matrix.{u1, u2, u3} o m α}, Iff (Eq.{max (max (max (max (succ u4) (succ u2)) (succ u5)) (succ u1)) (succ u3)} (Matrix.{max u1 u5, max u2 u4, u3} (Sum.{u5, u1} n o) (Sum.{u4, u2} l m) α) (Matrix.fromBlocks.{u4, u2, u5, u1, u3} l m n o α A B C D) (Matrix.fromBlocks.{u4, u2, u5, u1, u3} l m n o α A' B' C' D')) (And (Eq.{max (max (succ u4) (succ u5)) (succ u3)} (Matrix.{u5, u4, u3} n l α) A A') (And (Eq.{max (max (succ u2) (succ u5)) (succ u3)} (Matrix.{u5, u2, u3} n m α) B B') (And (Eq.{max (max (succ u4) (succ u1)) (succ u3)} (Matrix.{u1, u4, u3} o l α) C C') (Eq.{max (max (succ u2) (succ u1)) (succ u3)} (Matrix.{u1, u2, u3} o m α) D D'))))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_inj Matrix.fromBlocks_injₓ'. -/
@[simp]
theorem fromBlocks_inj {A : Matrix n l α} {B : Matrix n m α} {C : Matrix o l α} {D : Matrix o m α}
    {A' : Matrix n l α} {B' : Matrix n m α} {C' : Matrix o l α} {D' : Matrix o m α} :
    fromBlocks A B C D = fromBlocks A' B' C' D' ↔ A = A' ∧ B = B' ∧ C = C' ∧ D = D' :=
  ext_iff_blocks
#align matrix.from_blocks_inj Matrix.fromBlocks_inj

/- warning: matrix.from_blocks_map -> Matrix.fromBlocks_map is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} {β : Type.{u6}} (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α) (f : α -> β), Eq.{succ (max (max u3 u4) (max u1 u2) u6)} (Matrix.{max u3 u4, max u1 u2, u6} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) β) (Matrix.map.{u5, u6, max u3 u4, max u1 u2} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α β (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D) f) (Matrix.fromBlocks.{u1, u2, u3, u4, u6} l m n o β (Matrix.map.{u5, u6, u3, u1} n l α β A f) (Matrix.map.{u5, u6, u3, u2} n m α β B f) (Matrix.map.{u5, u6, u4, u1} o l α β C f) (Matrix.map.{u5, u6, u4, u2} o m α β D f))
but is expected to have type
  forall {l : Type.{u5}} {m : Type.{u3}} {n : Type.{u6}} {o : Type.{u2}} {α : Type.{u4}} {β : Type.{u1}} (A : Matrix.{u6, u5, u4} n l α) (B : Matrix.{u6, u3, u4} n m α) (C : Matrix.{u2, u5, u4} o l α) (D : Matrix.{u2, u3, u4} o m α) (f : α -> β), Eq.{max (max (max (max (succ u5) (succ u3)) (succ u6)) (succ u2)) (succ u1)} (Matrix.{max u6 u2, max u5 u3, u1} (Sum.{u6, u2} n o) (Sum.{u5, u3} l m) β) (Matrix.map.{u4, u1, max u6 u2, max u5 u3} (Sum.{u6, u2} n o) (Sum.{u5, u3} l m) α β (Matrix.fromBlocks.{u5, u3, u6, u2, u4} l m n o α A B C D) f) (Matrix.fromBlocks.{u5, u3, u6, u2, u1} l m n o β (Matrix.map.{u4, u1, u6, u5} n l α β A f) (Matrix.map.{u4, u1, u6, u3} n m α β B f) (Matrix.map.{u4, u1, u2, u5} o l α β C f) (Matrix.map.{u4, u1, u2, u3} o m α β D f))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_map Matrix.fromBlocks_mapₓ'. -/
theorem fromBlocks_map (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
    (f : α → β) : (fromBlocks A B C D).map f = fromBlocks (A.map f) (B.map f) (C.map f) (D.map f) :=
  by ext (i j); rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [from_blocks]
#align matrix.from_blocks_map Matrix.fromBlocks_map

/- warning: matrix.from_blocks_transpose -> Matrix.fromBlocks_transpose is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α), Eq.{succ (max (max u1 u2) (max u3 u4) u5)} (Matrix.{max u1 u2, max u3 u4, u5} (Sum.{u1, u2} l m) (Sum.{u3, u4} n o) α) (Matrix.transpose.{u5, max u3 u4, max u1 u2} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D)) (Matrix.fromBlocks.{u3, u4, u1, u2, u5} n o l m α (Matrix.transpose.{u5, u3, u1} n l α A) (Matrix.transpose.{u5, u4, u1} o l α C) (Matrix.transpose.{u5, u3, u2} n m α B) (Matrix.transpose.{u5, u4, u2} o m α D))
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u2}} {n : Type.{u5}} {o : Type.{u1}} {α : Type.{u3}} (A : Matrix.{u5, u4, u3} n l α) (B : Matrix.{u5, u2, u3} n m α) (C : Matrix.{u1, u4, u3} o l α) (D : Matrix.{u1, u2, u3} o m α), Eq.{max (max (max (max (succ u4) (succ u2)) (succ u5)) (succ u1)) (succ u3)} (Matrix.{max u2 u4, max u1 u5, u3} (Sum.{u4, u2} l m) (Sum.{u5, u1} n o) α) (Matrix.transpose.{u3, max u1 u5, max u2 u4} (Sum.{u5, u1} n o) (Sum.{u4, u2} l m) α (Matrix.fromBlocks.{u4, u2, u5, u1, u3} l m n o α A B C D)) (Matrix.fromBlocks.{u5, u1, u4, u2, u3} n o l m α (Matrix.transpose.{u3, u5, u4} n l α A) (Matrix.transpose.{u3, u1, u4} o l α C) (Matrix.transpose.{u3, u5, u2} n m α B) (Matrix.transpose.{u3, u1, u2} o m α D))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_transpose Matrix.fromBlocks_transposeₓ'. -/
theorem fromBlocks_transpose (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ := by ext (i j);
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [from_blocks]
#align matrix.from_blocks_transpose Matrix.fromBlocks_transpose

/- warning: matrix.from_blocks_conj_transpose -> Matrix.fromBlocks_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} [_inst_1 : Star.{u5} α] (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α), Eq.{succ (max (max u1 u2) (max u3 u4) u5)} (Matrix.{max u1 u2, max u3 u4, u5} (Sum.{u1, u2} l m) (Sum.{u3, u4} n o) α) (Matrix.conjTranspose.{u5, max u3 u4, max u1 u2} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α _inst_1 (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D)) (Matrix.fromBlocks.{u3, u4, u1, u2, u5} n o l m α (Matrix.conjTranspose.{u5, u3, u1} n l α _inst_1 A) (Matrix.conjTranspose.{u5, u4, u1} o l α _inst_1 C) (Matrix.conjTranspose.{u5, u3, u2} n m α _inst_1 B) (Matrix.conjTranspose.{u5, u4, u2} o m α _inst_1 D))
but is expected to have type
  forall {l : Type.{u3}} {m : Type.{u2}} {n : Type.{u4}} {o : Type.{u1}} {α : Type.{u5}} [_inst_1 : Star.{u5} α] (A : Matrix.{u4, u3, u5} n l α) (B : Matrix.{u4, u2, u5} n m α) (C : Matrix.{u1, u3, u5} o l α) (D : Matrix.{u1, u2, u5} o m α), Eq.{max (max (max (max (succ u3) (succ u2)) (succ u4)) (succ u1)) (succ u5)} (Matrix.{max u2 u3, max u1 u4, u5} (Sum.{u3, u2} l m) (Sum.{u4, u1} n o) α) (Matrix.conjTranspose.{u5, max u1 u4, max u2 u3} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) α _inst_1 (Matrix.fromBlocks.{u3, u2, u4, u1, u5} l m n o α A B C D)) (Matrix.fromBlocks.{u4, u1, u3, u2, u5} n o l m α (Matrix.conjTranspose.{u5, u4, u3} n l α _inst_1 A) (Matrix.conjTranspose.{u5, u1, u3} o l α _inst_1 C) (Matrix.conjTranspose.{u5, u4, u2} n m α _inst_1 B) (Matrix.conjTranspose.{u5, u1, u2} o m α _inst_1 D))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_conj_transpose Matrix.fromBlocks_conjTransposeₓ'. -/
theorem fromBlocks_conjTranspose [Star α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᴴ = fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ := by
  simp only [conj_transpose, from_blocks_transpose, from_blocks_map]
#align matrix.from_blocks_conj_transpose Matrix.fromBlocks_conjTranspose

/- warning: matrix.from_blocks_submatrix_sum_swap_left -> Matrix.fromBlocks_submatrix_sum_swap_left is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {p : Type.{u5}} {α : Type.{u6}} (A : Matrix.{u3, u1, u6} n l α) (B : Matrix.{u3, u2, u6} n m α) (C : Matrix.{u4, u1, u6} o l α) (D : Matrix.{u4, u2, u6} o m α) (f : p -> (Sum.{u1, u2} l m)), Eq.{succ (max (max u4 u3) u5 u6)} (Matrix.{max u4 u3, u5, u6} (Sum.{u4, u3} o n) p α) (Matrix.submatrix.{u6, max u4 u3, max u3 u4, max u1 u2, u5} (Sum.{u4, u3} o n) (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) p α (Matrix.fromBlocks.{u1, u2, u3, u4, u6} l m n o α A B C D) (Sum.swap.{u4, u3} o n) f) (Matrix.submatrix.{u6, max u4 u3, max u4 u3, max u1 u2, u5} (Sum.{u4, u3} o n) (Sum.{u4, u3} o n) (Sum.{u1, u2} l m) p α (Matrix.fromBlocks.{u1, u2, u4, u3, u6} l m o n α C D A B) (id.{max (succ u4) (succ u3)} (Sum.{u4, u3} o n)) f)
but is expected to have type
  forall {l : Type.{u5}} {m : Type.{u3}} {n : Type.{u6}} {o : Type.{u2}} {p : Type.{u1}} {α : Type.{u4}} (A : Matrix.{u6, u5, u4} n l α) (B : Matrix.{u6, u3, u4} n m α) (C : Matrix.{u2, u5, u4} o l α) (D : Matrix.{u2, u3, u4} o m α) (f : p -> (Sum.{u5, u3} l m)), Eq.{max (max (max (succ u6) (succ u2)) (succ u1)) (succ u4)} (Matrix.{max u6 u2, u1, u4} (Sum.{u2, u6} o n) p α) (Matrix.submatrix.{u4, max u6 u2, max u6 u2, max u5 u3, u1} (Sum.{u2, u6} o n) (Sum.{u6, u2} n o) (Sum.{u5, u3} l m) p α (Matrix.fromBlocks.{u5, u3, u6, u2, u4} l m n o α A B C D) (Sum.swap.{u2, u6} o n) f) (Matrix.submatrix.{u4, max u6 u2, max u6 u2, max u5 u3, u1} (Sum.{u2, u6} o n) (Sum.{u2, u6} o n) (Sum.{u5, u3} l m) p α (Matrix.fromBlocks.{u5, u3, u2, u6, u4} l m o n α C D A B) (id.{succ (max u6 u2)} (Sum.{u2, u6} o n)) f)
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_submatrix_sum_swap_left Matrix.fromBlocks_submatrix_sum_swap_leftₓ'. -/
@[simp]
theorem fromBlocks_submatrix_sum_swap_left (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (f : p → Sum l m) :
    (fromBlocks A B C D).submatrix Sum.swap f = (fromBlocks C D A B).submatrix id f := by ext (i j);
  cases i <;> dsimp <;> cases f j <;> rfl
#align matrix.from_blocks_submatrix_sum_swap_left Matrix.fromBlocks_submatrix_sum_swap_left

/- warning: matrix.from_blocks_submatrix_sum_swap_right -> Matrix.fromBlocks_submatrix_sum_swap_right is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {p : Type.{u5}} {α : Type.{u6}} (A : Matrix.{u3, u1, u6} n l α) (B : Matrix.{u3, u2, u6} n m α) (C : Matrix.{u4, u1, u6} o l α) (D : Matrix.{u4, u2, u6} o m α) (f : p -> (Sum.{u3, u4} n o)), Eq.{succ (max u5 (max u2 u1) u6)} (Matrix.{u5, max u2 u1, u6} p (Sum.{u2, u1} m l) α) (Matrix.submatrix.{u6, u5, max u3 u4, max u1 u2, max u2 u1} p (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) (Sum.{u2, u1} m l) α (Matrix.fromBlocks.{u1, u2, u3, u4, u6} l m n o α A B C D) f (Sum.swap.{u2, u1} m l)) (Matrix.submatrix.{u6, u5, max u3 u4, max u2 u1, max u2 u1} p (Sum.{u3, u4} n o) (Sum.{u2, u1} m l) (Sum.{u2, u1} m l) α (Matrix.fromBlocks.{u2, u1, u3, u4, u6} m l n o α B A D C) f (id.{max (succ u2) (succ u1)} (Sum.{u2, u1} m l)))
but is expected to have type
  forall {l : Type.{u5}} {m : Type.{u3}} {n : Type.{u6}} {o : Type.{u2}} {p : Type.{u1}} {α : Type.{u4}} (A : Matrix.{u6, u5, u4} n l α) (B : Matrix.{u6, u3, u4} n m α) (C : Matrix.{u2, u5, u4} o l α) (D : Matrix.{u2, u3, u4} o m α) (f : p -> (Sum.{u6, u2} n o)), Eq.{max (max (max (succ u5) (succ u3)) (succ u1)) (succ u4)} (Matrix.{u1, max u5 u3, u4} p (Sum.{u3, u5} m l) α) (Matrix.submatrix.{u4, u1, max u6 u2, max u5 u3, max u5 u3} p (Sum.{u6, u2} n o) (Sum.{u5, u3} l m) (Sum.{u3, u5} m l) α (Matrix.fromBlocks.{u5, u3, u6, u2, u4} l m n o α A B C D) f (Sum.swap.{u3, u5} m l)) (Matrix.submatrix.{u4, u1, max u6 u2, max u5 u3, max u5 u3} p (Sum.{u6, u2} n o) (Sum.{u3, u5} m l) (Sum.{u3, u5} m l) α (Matrix.fromBlocks.{u3, u5, u6, u2, u4} m l n o α B A D C) f (id.{succ (max u5 u3)} (Sum.{u3, u5} m l)))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_submatrix_sum_swap_right Matrix.fromBlocks_submatrix_sum_swap_rightₓ'. -/
@[simp]
theorem fromBlocks_submatrix_sum_swap_right (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (f : p → Sum n o) :
    (fromBlocks A B C D).submatrix f Sum.swap = (fromBlocks B A D C).submatrix f id := by ext (i j);
  cases j <;> dsimp <;> cases f i <;> rfl
#align matrix.from_blocks_submatrix_sum_swap_right Matrix.fromBlocks_submatrix_sum_swap_right

/- warning: matrix.from_blocks_submatrix_sum_swap_sum_swap -> Matrix.fromBlocks_submatrix_sum_swap_sum_swap is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α), Eq.{succ (max (max u4 u3) (max u2 u1) u5)} (Matrix.{max u4 u3, max u2 u1, u5} (Sum.{u4, u3} o n) (Sum.{u2, u1} m l) α) (Matrix.submatrix.{u5, max u4 u3, max u3 u4, max u1 u2, max u2 u1} (Sum.{u4, u3} o n) (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) (Sum.{u2, u1} m l) α (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D) (Sum.swap.{u4, u3} o n) (Sum.swap.{u2, u1} m l)) (Matrix.fromBlocks.{u2, u1, u4, u3, u5} m l o n α D C B A)
but is expected to have type
  forall {l : Type.{u5}} {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u2}} {α : Type.{u1}} (A : Matrix.{u3, u5, u1} n l α) (B : Matrix.{u3, u4, u1} n m α) (C : Matrix.{u2, u5, u1} o l α) (D : Matrix.{u2, u4, u1} o m α), Eq.{max (max (max (max (succ u5) (succ u4)) (succ u3)) (succ u2)) (succ u1)} (Matrix.{max u3 u2, max u5 u4, u1} (Sum.{u2, u3} o n) (Sum.{u4, u5} m l) α) (Matrix.submatrix.{u1, max u3 u2, max u3 u2, max u5 u4, max u5 u4} (Sum.{u2, u3} o n) (Sum.{u3, u2} n o) (Sum.{u5, u4} l m) (Sum.{u4, u5} m l) α (Matrix.fromBlocks.{u5, u4, u3, u2, u1} l m n o α A B C D) (Sum.swap.{u2, u3} o n) (Sum.swap.{u4, u5} m l)) (Matrix.fromBlocks.{u4, u5, u2, u3, u1} m l o n α D C B A)
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_submatrix_sum_swap_sum_swap Matrix.fromBlocks_submatrix_sum_swap_sum_swapₓ'. -/
theorem fromBlocks_submatrix_sum_swap_sum_swap {l m n o α : Type _} (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).submatrix Sum.swap Sum.swap = fromBlocks D C B A := by simp
#align matrix.from_blocks_submatrix_sum_swap_sum_swap Matrix.fromBlocks_submatrix_sum_swap_sum_swap

#print Matrix.IsTwoBlockDiagonal /-
/-- A 2x2 block matrix is block diagonal if the blocks outside of the diagonal vanish -/
def IsTwoBlockDiagonal [Zero α] (A : Matrix (Sum n o) (Sum l m) α) : Prop :=
  toBlocks₁₂ A = 0 ∧ toBlocks₂₁ A = 0
#align matrix.is_two_block_diagonal Matrix.IsTwoBlockDiagonal
-/

#print Matrix.toBlock /-
/-- Let `p` pick out certain rows and `q` pick out certain columns of a matrix `M`. Then
  `to_block M p q` is the corresponding block matrix. -/
def toBlock (M : Matrix m n α) (p : m → Prop) (q : n → Prop) : Matrix { a // p a } { a // q a } α :=
  M.submatrix coe coe
#align matrix.to_block Matrix.toBlock
-/

/- warning: matrix.to_block_apply -> Matrix.toBlock_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} (M : Matrix.{u1, u2, u3} m n α) (p : m -> Prop) (q : n -> Prop) (i : Subtype.{succ u1} m (fun (a : m) => p a)) (j : Subtype.{succ u2} n (fun (a : n) => q a)), Eq.{succ u3} α (Matrix.toBlock.{u1, u2, u3} m n α M p q i j) (M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} m (fun (a : m) => p a)) m (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => p a)) m (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => p a)) m (coeBase.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => p a)) m (coeSubtype.{succ u1} m (fun (a : m) => p a))))) i) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} n (fun (a : n) => q a)) n (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} n (fun (a : n) => q a)) n (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} n (fun (a : n) => q a)) n (coeBase.{succ u2, succ u2} (Subtype.{succ u2} n (fun (a : n) => q a)) n (coeSubtype.{succ u2} n (fun (a : n) => q a))))) j))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u1}} (M : Matrix.{u3, u2, u1} m n α) (p : m -> Prop) (q : n -> Prop) (i : Subtype.{succ u3} m (fun (a : m) => p a)) (j : Subtype.{succ u2} n (fun (a : n) => q a)), Eq.{succ u1} α (Matrix.toBlock.{u3, u2, u1} m n α M p q i j) (M (Subtype.val.{succ u3} m (fun (a : m) => p a) i) (Subtype.val.{succ u2} n (fun (a : n) => q a) j))
Case conversion may be inaccurate. Consider using '#align matrix.to_block_apply Matrix.toBlock_applyₓ'. -/
@[simp]
theorem toBlock_apply (M : Matrix m n α) (p : m → Prop) (q : n → Prop) (i : { a // p a })
    (j : { a // q a }) : toBlock M p q i j = M ↑i ↑j :=
  rfl
#align matrix.to_block_apply Matrix.toBlock_apply

#print Matrix.toSquareBlockProp /-
/-- Let `p` pick out certain rows and columns of a square matrix `M`. Then
  `to_square_block_prop M p` is the corresponding block matrix. -/
def toSquareBlockProp (M : Matrix m m α) (p : m → Prop) : Matrix { a // p a } { a // p a } α :=
  toBlock M _ _
#align matrix.to_square_block_prop Matrix.toSquareBlockProp
-/

/- warning: matrix.to_square_block_prop_def -> Matrix.toSquareBlockProp_def is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {α : Type.{u2}} (M : Matrix.{u1, u1, u2} m m α) (p : m -> Prop), Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => p a)) α) (Matrix.toSquareBlockProp.{u1, u2} m α M p) (fun (i : Subtype.{succ u1} m (fun (a : m) => p a)) (j : Subtype.{succ u1} m (fun (a : m) => p a)) => M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} m (fun (a : m) => p a)) m (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => p a)) m (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => p a)) m (coeBase.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => p a)) m (coeSubtype.{succ u1} m (fun (a : m) => p a))))) i) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} m (fun (a : m) => p a)) m (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => p a)) m (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => p a)) m (coeBase.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => p a)) m (coeSubtype.{succ u1} m (fun (a : m) => p a))))) j))
but is expected to have type
  forall {m : Type.{u2}} {α : Type.{u1}} (M : Matrix.{u2, u2, u1} m m α) (p : m -> Prop), Eq.{max (succ u2) (succ u1)} (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => p a)) α) (Matrix.toSquareBlockProp.{u2, u1} m α M p) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} ((Subtype.{succ u2} m (fun (a : m) => p a)) -> (Subtype.{succ u2} m (fun (a : m) => p a)) -> α) (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => p a)) α)) ((Subtype.{succ u2} m (fun (a : m) => p a)) -> (Subtype.{succ u2} m (fun (a : m) => p a)) -> α) (fun (a : (Subtype.{succ u2} m (fun (a : m) => p a)) -> (Subtype.{succ u2} m (fun (a : m) => p a)) -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : (Subtype.{succ u2} m (fun (a : m) => p a)) -> (Subtype.{succ u2} m (fun (a : m) => p a)) -> α) => Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => p a)) α) a) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} ((Subtype.{succ u2} m (fun (a : m) => p a)) -> (Subtype.{succ u2} m (fun (a : m) => p a)) -> α) (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => p a)) α)) (Matrix.of.{u1, u2, u2} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => p a)) α) (fun (i : Subtype.{succ u2} m (fun (a : m) => p a)) (j : Subtype.{succ u2} m (fun (a : m) => p a)) => M (Subtype.val.{succ u2} m (fun (a : m) => p a) i) (Subtype.val.{succ u2} m (fun (a : m) => p a) j)))
Case conversion may be inaccurate. Consider using '#align matrix.to_square_block_prop_def Matrix.toSquareBlockProp_defₓ'. -/
theorem toSquareBlockProp_def (M : Matrix m m α) (p : m → Prop) :
    toSquareBlockProp M p = fun i j => M ↑i ↑j :=
  rfl
#align matrix.to_square_block_prop_def Matrix.toSquareBlockProp_def

#print Matrix.toSquareBlock /-
/-- Let `b` map rows and columns of a square matrix `M` to blocks. Then
  `to_square_block M b k` is the block `k` matrix. -/
def toSquareBlock (M : Matrix m m α) (b : m → β) (k : β) :
    Matrix { a // b a = k } { a // b a = k } α :=
  toSquareBlockProp M _
#align matrix.to_square_block Matrix.toSquareBlock
-/

/- warning: matrix.to_square_block_def -> Matrix.toSquareBlock_def is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} (M : Matrix.{u1, u1, u2} m m α) (b : m -> β) (k : β), Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) (Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) α) (Matrix.toSquareBlock.{u1, u2, u3} m α β M b k) (fun (i : Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) (j : Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) => M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) m (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) m (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) m (coeBase.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) m (coeSubtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k))))) i) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) m (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) m (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) m (coeBase.{succ u1, succ u1} (Subtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k)) m (coeSubtype.{succ u1} m (fun (a : m) => Eq.{succ u3} β (b a) k))))) j))
but is expected to have type
  forall {m : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} (M : Matrix.{u3, u3, u2} m m α) (b : m -> β) (k : β), Eq.{max (succ u3) (succ u2)} (Matrix.{u3, u3, u2} (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) α) (Matrix.toSquareBlock.{u3, u2, u1} m α β M b k) (FunLike.coe.{max (succ u3) (succ u2), max (succ u3) (succ u2), max (succ u3) (succ u2)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} ((Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) -> (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) -> α) (Matrix.{u3, u3, u2} (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) α)) ((Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) -> (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) -> α) (fun (a : (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) -> (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) -> (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) -> α) => Matrix.{u3, u3, u2} (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) α) a) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u2), max (succ u3) (succ u2)} ((Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) -> (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) -> α) (Matrix.{u3, u3, u2} (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) α)) (Matrix.of.{u2, u3, u3} (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) (Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) α) (fun (i : Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) (j : Subtype.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k)) => M (Subtype.val.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k) i) (Subtype.val.{succ u3} m (fun (a : m) => Eq.{succ u1} β (b a) k) j)))
Case conversion may be inaccurate. Consider using '#align matrix.to_square_block_def Matrix.toSquareBlock_defₓ'. -/
theorem toSquareBlock_def (M : Matrix m m α) (b : m → β) (k : β) :
    toSquareBlock M b k = fun i j => M ↑i ↑j :=
  rfl
#align matrix.to_square_block_def Matrix.toSquareBlock_def

/- warning: matrix.from_blocks_smul -> Matrix.fromBlocks_smul is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {R : Type.{u5}} {α : Type.{u6}} [_inst_1 : SMul.{u5, u6} R α] (x : R) (A : Matrix.{u3, u1, u6} n l α) (B : Matrix.{u3, u2, u6} n m α) (C : Matrix.{u4, u1, u6} o l α) (D : Matrix.{u4, u2, u6} o m α), Eq.{succ (max (max u3 u4) (max u1 u2) u6)} (Matrix.{max u3 u4, max u1 u2, u6} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) (SMul.smul.{u5, max (max u3 u4) (max u1 u2) u6} R (Matrix.{max u3 u4, max u1 u2, u6} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) (Matrix.hasSmul.{u6, max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) R α _inst_1) x (Matrix.fromBlocks.{u1, u2, u3, u4, u6} l m n o α A B C D)) (Matrix.fromBlocks.{u1, u2, u3, u4, u6} l m n o α (SMul.smul.{u5, max u3 u1 u6} R (Matrix.{u3, u1, u6} n l α) (Matrix.hasSmul.{u6, u3, u1, u5} n l R α _inst_1) x A) (SMul.smul.{u5, max u3 u2 u6} R (Matrix.{u3, u2, u6} n m α) (Matrix.hasSmul.{u6, u3, u2, u5} n m R α _inst_1) x B) (SMul.smul.{u5, max u4 u1 u6} R (Matrix.{u4, u1, u6} o l α) (Matrix.hasSmul.{u6, u4, u1, u5} o l R α _inst_1) x C) (SMul.smul.{u5, max u4 u2 u6} R (Matrix.{u4, u2, u6} o m α) (Matrix.hasSmul.{u6, u4, u2, u5} o m R α _inst_1) x D))
but is expected to have type
  forall {l : Type.{u3}} {m : Type.{u2}} {n : Type.{u4}} {o : Type.{u1}} {R : Type.{u6}} {α : Type.{u5}} [_inst_1 : SMul.{u6, u5} R α] (x : R) (A : Matrix.{u4, u3, u5} n l α) (B : Matrix.{u4, u2, u5} n m α) (C : Matrix.{u1, u3, u5} o l α) (D : Matrix.{u1, u2, u5} o m α), Eq.{max (max (max (max (succ u3) (succ u2)) (succ u4)) (succ u1)) (succ u5)} (Matrix.{max u1 u4, max u2 u3, u5} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) α) (HSMul.hSMul.{u6, max (max (max (max u5 u1) u4) u2) u3, max (max (max (max u3 u2) u4) u1) u5} R (Matrix.{max u1 u4, max u2 u3, u5} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) α) (Matrix.{max u1 u4, max u2 u3, u5} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) α) (instHSMul.{u6, max (max (max (max u3 u2) u4) u1) u5} R (Matrix.{max u1 u4, max u2 u3, u5} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) α) (Matrix.smul.{u5, max u4 u1, max u3 u2, u6} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) R α _inst_1)) x (Matrix.fromBlocks.{u3, u2, u4, u1, u5} l m n o α A B C D)) (Matrix.fromBlocks.{u3, u2, u4, u1, u5} l m n o α (HSMul.hSMul.{u6, max (max u3 u4) u5, max (max u3 u4) u5} R (Matrix.{u4, u3, u5} n l α) (Matrix.{u4, u3, u5} n l α) (instHSMul.{u6, max (max u3 u4) u5} R (Matrix.{u4, u3, u5} n l α) (Matrix.smul.{u5, u4, u3, u6} n l R α _inst_1)) x A) (HSMul.hSMul.{u6, max (max u2 u4) u5, max (max u2 u4) u5} R (Matrix.{u4, u2, u5} n m α) (Matrix.{u4, u2, u5} n m α) (instHSMul.{u6, max (max u2 u4) u5} R (Matrix.{u4, u2, u5} n m α) (Matrix.smul.{u5, u4, u2, u6} n m R α _inst_1)) x B) (HSMul.hSMul.{u6, max (max u3 u1) u5, max (max u3 u1) u5} R (Matrix.{u1, u3, u5} o l α) (Matrix.{u1, u3, u5} o l α) (instHSMul.{u6, max (max u3 u1) u5} R (Matrix.{u1, u3, u5} o l α) (Matrix.smul.{u5, u1, u3, u6} o l R α _inst_1)) x C) (HSMul.hSMul.{u6, max (max u2 u1) u5, max (max u2 u1) u5} R (Matrix.{u1, u2, u5} o m α) (Matrix.{u1, u2, u5} o m α) (instHSMul.{u6, max (max u2 u1) u5} R (Matrix.{u1, u2, u5} o m α) (Matrix.smul.{u5, u1, u2, u6} o m R α _inst_1)) x D))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_smul Matrix.fromBlocks_smulₓ'. -/
theorem fromBlocks_smul [SMul R α] (x : R) (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : x • fromBlocks A B C D = fromBlocks (x • A) (x • B) (x • C) (x • D) := by
  ext (i j); rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [from_blocks]
#align matrix.from_blocks_smul Matrix.fromBlocks_smul

/- warning: matrix.from_blocks_neg -> Matrix.fromBlocks_neg is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {R : Type.{u5}} [_inst_1 : Neg.{u5} R] (A : Matrix.{u3, u1, u5} n l R) (B : Matrix.{u3, u2, u5} n m R) (C : Matrix.{u4, u1, u5} o l R) (D : Matrix.{u4, u2, u5} o m R), Eq.{succ (max (max u3 u4) (max u1 u2) u5)} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) R) (Neg.neg.{max (max u3 u4) (max u1 u2) u5} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) R) (Matrix.hasNeg.{u5, max u3 u4, max u1 u2} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) R _inst_1) (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o R A B C D)) (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o R (Neg.neg.{max u3 u1 u5} (Matrix.{u3, u1, u5} n l R) (Matrix.hasNeg.{u5, u3, u1} n l R _inst_1) A) (Neg.neg.{max u3 u2 u5} (Matrix.{u3, u2, u5} n m R) (Matrix.hasNeg.{u5, u3, u2} n m R _inst_1) B) (Neg.neg.{max u4 u1 u5} (Matrix.{u4, u1, u5} o l R) (Matrix.hasNeg.{u5, u4, u1} o l R _inst_1) C) (Neg.neg.{max u4 u2 u5} (Matrix.{u4, u2, u5} o m R) (Matrix.hasNeg.{u5, u4, u2} o m R _inst_1) D))
but is expected to have type
  forall {l : Type.{u3}} {m : Type.{u2}} {n : Type.{u4}} {o : Type.{u1}} {R : Type.{u5}} [_inst_1 : Neg.{u5} R] (A : Matrix.{u4, u3, u5} n l R) (B : Matrix.{u4, u2, u5} n m R) (C : Matrix.{u1, u3, u5} o l R) (D : Matrix.{u1, u2, u5} o m R), Eq.{max (max (max (max (succ u3) (succ u2)) (succ u4)) (succ u1)) (succ u5)} (Matrix.{max u1 u4, max u2 u3, u5} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) R) (Neg.neg.{max (max (max (max u3 u2) u4) u1) u5} (Matrix.{max u1 u4, max u2 u3, u5} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) R) (Matrix.neg.{u5, max u4 u1, max u3 u2} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) R _inst_1) (Matrix.fromBlocks.{u3, u2, u4, u1, u5} l m n o R A B C D)) (Matrix.fromBlocks.{u3, u2, u4, u1, u5} l m n o R (Neg.neg.{max (max u3 u4) u5} (Matrix.{u4, u3, u5} n l R) (Matrix.neg.{u5, u4, u3} n l R _inst_1) A) (Neg.neg.{max (max u2 u4) u5} (Matrix.{u4, u2, u5} n m R) (Matrix.neg.{u5, u4, u2} n m R _inst_1) B) (Neg.neg.{max (max u3 u1) u5} (Matrix.{u1, u3, u5} o l R) (Matrix.neg.{u5, u1, u3} o l R _inst_1) C) (Neg.neg.{max (max u2 u1) u5} (Matrix.{u1, u2, u5} o m R) (Matrix.neg.{u5, u1, u2} o m R _inst_1) D))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_neg Matrix.fromBlocks_negₓ'. -/
theorem fromBlocks_neg [Neg R] (A : Matrix n l R) (B : Matrix n m R) (C : Matrix o l R)
    (D : Matrix o m R) : -fromBlocks A B C D = fromBlocks (-A) (-B) (-C) (-D) := by ext (i j);
  cases i <;> cases j <;> simp [from_blocks]
#align matrix.from_blocks_neg Matrix.fromBlocks_neg

/- warning: matrix.from_blocks_zero -> Matrix.fromBlocks_zero is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} [_inst_1 : Zero.{u5} α], Eq.{succ (max (max u3 u4) (max u1 u2) u5)} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α (OfNat.ofNat.{max u3 u1 u5} (Matrix.{u3, u1, u5} n l α) 0 (OfNat.mk.{max u3 u1 u5} (Matrix.{u3, u1, u5} n l α) 0 (Zero.zero.{max u3 u1 u5} (Matrix.{u3, u1, u5} n l α) (Matrix.hasZero.{u5, u3, u1} n l α _inst_1)))) (OfNat.ofNat.{max u3 u2 u5} (Matrix.{u3, u2, u5} n m α) 0 (OfNat.mk.{max u3 u2 u5} (Matrix.{u3, u2, u5} n m α) 0 (Zero.zero.{max u3 u2 u5} (Matrix.{u3, u2, u5} n m α) (Matrix.hasZero.{u5, u3, u2} n m α _inst_1)))) (OfNat.ofNat.{max u4 u1 u5} (Matrix.{u4, u1, u5} o l α) 0 (OfNat.mk.{max u4 u1 u5} (Matrix.{u4, u1, u5} o l α) 0 (Zero.zero.{max u4 u1 u5} (Matrix.{u4, u1, u5} o l α) (Matrix.hasZero.{u5, u4, u1} o l α _inst_1)))) (OfNat.ofNat.{max u4 u2 u5} (Matrix.{u4, u2, u5} o m α) 0 (OfNat.mk.{max u4 u2 u5} (Matrix.{u4, u2, u5} o m α) 0 (Zero.zero.{max u4 u2 u5} (Matrix.{u4, u2, u5} o m α) (Matrix.hasZero.{u5, u4, u2} o m α _inst_1))))) (OfNat.ofNat.{max (max u3 u4) (max u1 u2) u5} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) 0 (OfNat.mk.{max (max u3 u4) (max u1 u2) u5} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) 0 (Zero.zero.{max (max u3 u4) (max u1 u2) u5} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) (Matrix.hasZero.{u5, max u3 u4, max u1 u2} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α _inst_1))))
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u5}} [_inst_1 : Zero.{u5} α], Eq.{max (max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)) (succ u5)} (Matrix.{max u1 u2, max u3 u4, u5} (Sum.{u2, u1} n o) (Sum.{u4, u3} l m) α) (Matrix.fromBlocks.{u4, u3, u2, u1, u5} l m n o α (OfNat.ofNat.{max (max u4 u2) u5} (Matrix.{u2, u4, u5} n l α) 0 (Zero.toOfNat0.{max (max u4 u2) u5} (Matrix.{u2, u4, u5} n l α) (Matrix.zero.{u5, u2, u4} n l α _inst_1))) (OfNat.ofNat.{max (max u2 u5) u3} (Matrix.{u2, u3, u5} n m α) 0 (Zero.toOfNat0.{max (max u2 u5) u3} (Matrix.{u2, u3, u5} n m α) (Matrix.zero.{u5, u2, u3} n m α _inst_1))) (OfNat.ofNat.{max (max u4 u5) u1} (Matrix.{u1, u4, u5} o l α) 0 (Zero.toOfNat0.{max (max u4 u5) u1} (Matrix.{u1, u4, u5} o l α) (Matrix.zero.{u5, u1, u4} o l α _inst_1))) (OfNat.ofNat.{max (max u3 u1) u5} (Matrix.{u1, u3, u5} o m α) 0 (Zero.toOfNat0.{max (max u3 u1) u5} (Matrix.{u1, u3, u5} o m α) (Matrix.zero.{u5, u1, u3} o m α _inst_1)))) (OfNat.ofNat.{max (max (max (max u4 u3) u2) u1) u5} (Matrix.{max u1 u2, max u3 u4, u5} (Sum.{u2, u1} n o) (Sum.{u4, u3} l m) α) 0 (Zero.toOfNat0.{max (max (max (max u4 u3) u2) u1) u5} (Matrix.{max u1 u2, max u3 u4, u5} (Sum.{u2, u1} n o) (Sum.{u4, u3} l m) α) (Matrix.zero.{u5, max u2 u1, max u4 u3} (Sum.{u2, u1} n o) (Sum.{u4, u3} l m) α _inst_1)))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_zero Matrix.fromBlocks_zeroₓ'. -/
@[simp]
theorem fromBlocks_zero [Zero α] : fromBlocks (0 : Matrix n l α) 0 0 (0 : Matrix o m α) = 0 := by
  ext (i j); rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
#align matrix.from_blocks_zero Matrix.fromBlocks_zero

/- warning: matrix.from_blocks_add -> Matrix.fromBlocks_add is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} [_inst_1 : Add.{u5} α] (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α) (A' : Matrix.{u3, u1, u5} n l α) (B' : Matrix.{u3, u2, u5} n m α) (C' : Matrix.{u4, u1, u5} o l α) (D' : Matrix.{u4, u2, u5} o m α), Eq.{succ (max (max u3 u4) (max u1 u2) u5)} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) (HAdd.hAdd.{max (max u3 u4) (max u1 u2) u5, max (max u3 u4) (max u1 u2) u5, max (max u3 u4) (max u1 u2) u5} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) (instHAdd.{max (max u3 u4) (max u1 u2) u5} (Matrix.{max u3 u4, max u1 u2, u5} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α) (Matrix.hasAdd.{u5, max u3 u4, max u1 u2} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α _inst_1)) (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D) (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A' B' C' D')) (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α (HAdd.hAdd.{max u3 u1 u5, max u3 u1 u5, max u3 u1 u5} (Matrix.{u3, u1, u5} n l α) (Matrix.{u3, u1, u5} n l α) (Matrix.{u3, u1, u5} n l α) (instHAdd.{max u3 u1 u5} (Matrix.{u3, u1, u5} n l α) (Matrix.hasAdd.{u5, u3, u1} n l α _inst_1)) A A') (HAdd.hAdd.{max u3 u2 u5, max u3 u2 u5, max u3 u2 u5} (Matrix.{u3, u2, u5} n m α) (Matrix.{u3, u2, u5} n m α) (Matrix.{u3, u2, u5} n m α) (instHAdd.{max u3 u2 u5} (Matrix.{u3, u2, u5} n m α) (Matrix.hasAdd.{u5, u3, u2} n m α _inst_1)) B B') (HAdd.hAdd.{max u4 u1 u5, max u4 u1 u5, max u4 u1 u5} (Matrix.{u4, u1, u5} o l α) (Matrix.{u4, u1, u5} o l α) (Matrix.{u4, u1, u5} o l α) (instHAdd.{max u4 u1 u5} (Matrix.{u4, u1, u5} o l α) (Matrix.hasAdd.{u5, u4, u1} o l α _inst_1)) C C') (HAdd.hAdd.{max u4 u2 u5, max u4 u2 u5, max u4 u2 u5} (Matrix.{u4, u2, u5} o m α) (Matrix.{u4, u2, u5} o m α) (Matrix.{u4, u2, u5} o m α) (instHAdd.{max u4 u2 u5} (Matrix.{u4, u2, u5} o m α) (Matrix.hasAdd.{u5, u4, u2} o m α _inst_1)) D D'))
but is expected to have type
  forall {l : Type.{u3}} {m : Type.{u2}} {n : Type.{u4}} {o : Type.{u1}} {α : Type.{u5}} [_inst_1 : Add.{u5} α] (A : Matrix.{u4, u3, u5} n l α) (B : Matrix.{u4, u2, u5} n m α) (C : Matrix.{u1, u3, u5} o l α) (D : Matrix.{u1, u2, u5} o m α) (A' : Matrix.{u4, u3, u5} n l α) (B' : Matrix.{u4, u2, u5} n m α) (C' : Matrix.{u1, u3, u5} o l α) (D' : Matrix.{u1, u2, u5} o m α), Eq.{max (max (max (max (succ u3) (succ u2)) (succ u4)) (succ u1)) (succ u5)} (Matrix.{max u1 u4, max u2 u3, u5} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) α) (HAdd.hAdd.{max (max (max (max u3 u2) u4) u1) u5, max (max (max (max u3 u2) u4) u1) u5, max (max (max (max u3 u2) u4) u1) u5} (Matrix.{max u1 u4, max u2 u3, u5} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) α) (Matrix.{max u1 u4, max u2 u3, u5} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) α) (Matrix.{max u1 u4, max u2 u3, u5} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) α) (instHAdd.{max (max (max (max u3 u2) u4) u1) u5} (Matrix.{max u1 u4, max u2 u3, u5} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) α) (Matrix.add.{u5, max u4 u1, max u3 u2} (Sum.{u4, u1} n o) (Sum.{u3, u2} l m) α _inst_1)) (Matrix.fromBlocks.{u3, u2, u4, u1, u5} l m n o α A B C D) (Matrix.fromBlocks.{u3, u2, u4, u1, u5} l m n o α A' B' C' D')) (Matrix.fromBlocks.{u3, u2, u4, u1, u5} l m n o α (HAdd.hAdd.{max (max u3 u4) u5, max (max u3 u4) u5, max (max u3 u4) u5} (Matrix.{u4, u3, u5} n l α) (Matrix.{u4, u3, u5} n l α) (Matrix.{u4, u3, u5} n l α) (instHAdd.{max (max u3 u4) u5} (Matrix.{u4, u3, u5} n l α) (Matrix.add.{u5, u4, u3} n l α _inst_1)) A A') (HAdd.hAdd.{max (max u2 u4) u5, max (max u2 u4) u5, max (max u2 u4) u5} (Matrix.{u4, u2, u5} n m α) (Matrix.{u4, u2, u5} n m α) (Matrix.{u4, u2, u5} n m α) (instHAdd.{max (max u2 u4) u5} (Matrix.{u4, u2, u5} n m α) (Matrix.add.{u5, u4, u2} n m α _inst_1)) B B') (HAdd.hAdd.{max (max u3 u1) u5, max (max u3 u1) u5, max (max u3 u1) u5} (Matrix.{u1, u3, u5} o l α) (Matrix.{u1, u3, u5} o l α) (Matrix.{u1, u3, u5} o l α) (instHAdd.{max (max u3 u1) u5} (Matrix.{u1, u3, u5} o l α) (Matrix.add.{u5, u1, u3} o l α _inst_1)) C C') (HAdd.hAdd.{max (max u2 u1) u5, max (max u2 u1) u5, max (max u2 u1) u5} (Matrix.{u1, u2, u5} o m α) (Matrix.{u1, u2, u5} o m α) (Matrix.{u1, u2, u5} o m α) (instHAdd.{max (max u2 u1) u5} (Matrix.{u1, u2, u5} o m α) (Matrix.add.{u5, u1, u2} o m α _inst_1)) D D'))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_add Matrix.fromBlocks_addₓ'. -/
theorem fromBlocks_add [Add α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (A' : Matrix n l α) (B' : Matrix n m α) (C' : Matrix o l α)
    (D' : Matrix o m α) :
    fromBlocks A B C D + fromBlocks A' B' C' D' = fromBlocks (A + A') (B + B') (C + C') (D + D') :=
  by ext (i j); rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
#align matrix.from_blocks_add Matrix.fromBlocks_add

/- warning: matrix.from_blocks_multiply -> Matrix.fromBlocks_multiply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_multiply Matrix.fromBlocks_multiplyₓ'. -/
theorem fromBlocks_multiply [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (A' : Matrix l p α) (B' : Matrix l q α)
    (C' : Matrix m p α) (D' : Matrix m q α) :
    fromBlocks A B C D ⬝ fromBlocks A' B' C' D' =
      fromBlocks (A ⬝ A' + B ⬝ C') (A ⬝ B' + B ⬝ D') (C ⬝ A' + D ⬝ C') (C ⬝ B' + D ⬝ D') :=
  by ext (i j);
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;>
    simp only [from_blocks, mul_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.add_apply, of_apply]
#align matrix.from_blocks_multiply Matrix.fromBlocks_multiply

/- warning: matrix.from_blocks_mul_vec -> Matrix.fromBlocks_mulVec is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} [_inst_1 : Fintype.{u1} l] [_inst_2 : Fintype.{u2} m] [_inst_3 : NonUnitalNonAssocSemiring.{u5} α] (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α) (x : (Sum.{u1, u2} l m) -> α), Eq.{max (succ (max u3 u4)) (succ u5)} ((Sum.{u3, u4} n o) -> α) (Matrix.mulVec.{u5, max u3 u4, max u1 u2} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α _inst_3 (Sum.fintype.{u1, u2} l m _inst_1 _inst_2) (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D) x) (Sum.elim.{u3, u4, succ u5} n o α (HAdd.hAdd.{max u3 u5, max u3 u5, max u3 u5} (n -> α) (n -> α) (n -> α) (instHAdd.{max u3 u5} (n -> α) (Pi.instAdd.{u3, u5} n (fun (ᾰ : n) => α) (fun (i : n) => Distrib.toHasAdd.{u5} α (NonUnitalNonAssocSemiring.toDistrib.{u5} α _inst_3)))) (Matrix.mulVec.{u5, u3, u1} n l α _inst_3 _inst_1 A (Function.comp.{succ u1, max (succ u1) (succ u2), succ u5} l (Sum.{u1, u2} l m) α x (Sum.inl.{u1, u2} l m))) (Matrix.mulVec.{u5, u3, u2} n m α _inst_3 _inst_2 B (Function.comp.{succ u2, max (succ u1) (succ u2), succ u5} m (Sum.{u1, u2} l m) α x (Sum.inr.{u1, u2} l m)))) (HAdd.hAdd.{max u4 u5, max u4 u5, max u4 u5} (o -> α) (o -> α) (o -> α) (instHAdd.{max u4 u5} (o -> α) (Pi.instAdd.{u4, u5} o (fun (ᾰ : o) => α) (fun (i : o) => Distrib.toHasAdd.{u5} α (NonUnitalNonAssocSemiring.toDistrib.{u5} α _inst_3)))) (Matrix.mulVec.{u5, u4, u1} o l α _inst_3 _inst_1 C (Function.comp.{succ u1, max (succ u1) (succ u2), succ u5} l (Sum.{u1, u2} l m) α x (Sum.inl.{u1, u2} l m))) (Matrix.mulVec.{u5, u4, u2} o m α _inst_3 _inst_2 D (Function.comp.{succ u2, max (succ u1) (succ u2), succ u5} m (Sum.{u1, u2} l m) α x (Sum.inr.{u1, u2} l m)))))
but is expected to have type
  forall {l : Type.{u5}} {m : Type.{u4}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u3}} [_inst_1 : Fintype.{u5} l] [_inst_2 : Fintype.{u4} m] [_inst_3 : NonUnitalNonAssocSemiring.{u3} α] (A : Matrix.{u2, u5, u3} n l α) (B : Matrix.{u2, u4, u3} n m α) (C : Matrix.{u1, u5, u3} o l α) (D : Matrix.{u1, u4, u3} o m α) (x : (Sum.{u5, u4} l m) -> α), Eq.{max (max (succ u2) (succ u1)) (succ u3)} ((Sum.{u2, u1} n o) -> α) (Matrix.mulVec.{u3, max u1 u2, max u4 u5} (Sum.{u2, u1} n o) (Sum.{u5, u4} l m) α _inst_3 (instFintypeSum.{u5, u4} l m _inst_1 _inst_2) (Matrix.fromBlocks.{u5, u4, u2, u1, u3} l m n o α A B C D) x) (Sum.elim.{u2, u1, succ u3} n o α (HAdd.hAdd.{max u2 u3, max u2 u3, max u2 u3} (n -> α) (n -> α) (n -> α) (instHAdd.{max u2 u3} (n -> α) (Pi.instAdd.{u2, u3} n (fun (ᾰ : n) => α) (fun (i : n) => Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3)))) (Matrix.mulVec.{u3, u2, u5} n l α _inst_3 _inst_1 A (Function.comp.{succ u5, max (succ u5) (succ u4), succ u3} l (Sum.{u5, u4} l m) α x (Sum.inl.{u5, u4} l m))) (Matrix.mulVec.{u3, u2, u4} n m α _inst_3 _inst_2 B (Function.comp.{succ u4, max (succ u5) (succ u4), succ u3} m (Sum.{u5, u4} l m) α x (Sum.inr.{u5, u4} l m)))) (HAdd.hAdd.{max u1 u3, max u1 u3, max u1 u3} (o -> α) (o -> α) (o -> α) (instHAdd.{max u1 u3} (o -> α) (Pi.instAdd.{u1, u3} o (fun (ᾰ : o) => α) (fun (i : o) => Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3)))) (Matrix.mulVec.{u3, u1, u5} o l α _inst_3 _inst_1 C (Function.comp.{succ u5, max (succ u5) (succ u4), succ u3} l (Sum.{u5, u4} l m) α x (Sum.inl.{u5, u4} l m))) (Matrix.mulVec.{u3, u1, u4} o m α _inst_3 _inst_2 D (Function.comp.{succ u4, max (succ u5) (succ u4), succ u3} m (Sum.{u5, u4} l m) α x (Sum.inr.{u5, u4} l m)))))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_mul_vec Matrix.fromBlocks_mulVecₓ'. -/
theorem fromBlocks_mulVec [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : Sum l m → α) :
    mulVec (fromBlocks A B C D) x =
      Sum.elim (mulVec A (x ∘ Sum.inl) + mulVec B (x ∘ Sum.inr))
        (mulVec C (x ∘ Sum.inl) + mulVec D (x ∘ Sum.inr)) :=
  by ext i; cases i <;> simp [mul_vec, dot_product]
#align matrix.from_blocks_mul_vec Matrix.fromBlocks_mulVec

/- warning: matrix.vec_mul_from_blocks -> Matrix.vecMul_fromBlocks is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u5}} [_inst_1 : Fintype.{u3} n] [_inst_2 : Fintype.{u4} o] [_inst_3 : NonUnitalNonAssocSemiring.{u5} α] (A : Matrix.{u3, u1, u5} n l α) (B : Matrix.{u3, u2, u5} n m α) (C : Matrix.{u4, u1, u5} o l α) (D : Matrix.{u4, u2, u5} o m α) (x : (Sum.{u3, u4} n o) -> α), Eq.{max (succ (max u1 u2)) (succ u5)} ((Sum.{u1, u2} l m) -> α) (Matrix.vecMul.{u5, max u3 u4, max u1 u2} (Sum.{u3, u4} n o) (Sum.{u1, u2} l m) α _inst_3 (Sum.fintype.{u3, u4} n o _inst_1 _inst_2) x (Matrix.fromBlocks.{u1, u2, u3, u4, u5} l m n o α A B C D)) (Sum.elim.{u1, u2, succ u5} l m α (HAdd.hAdd.{max u1 u5, max u1 u5, max u1 u5} (l -> α) (l -> α) (l -> α) (instHAdd.{max u1 u5} (l -> α) (Pi.instAdd.{u1, u5} l (fun (ᾰ : l) => α) (fun (i : l) => Distrib.toHasAdd.{u5} α (NonUnitalNonAssocSemiring.toDistrib.{u5} α _inst_3)))) (Matrix.vecMul.{u5, u3, u1} n l α _inst_3 _inst_1 (Function.comp.{succ u3, max (succ u3) (succ u4), succ u5} n (Sum.{u3, u4} n o) α x (Sum.inl.{u3, u4} n o)) A) (Matrix.vecMul.{u5, u4, u1} o l α _inst_3 _inst_2 (Function.comp.{succ u4, max (succ u3) (succ u4), succ u5} o (Sum.{u3, u4} n o) α x (Sum.inr.{u3, u4} n o)) C)) (HAdd.hAdd.{max u2 u5, max u2 u5, max u2 u5} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u5} (m -> α) (Pi.instAdd.{u2, u5} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toHasAdd.{u5} α (NonUnitalNonAssocSemiring.toDistrib.{u5} α _inst_3)))) (Matrix.vecMul.{u5, u3, u2} n m α _inst_3 _inst_1 (Function.comp.{succ u3, max (succ u3) (succ u4), succ u5} n (Sum.{u3, u4} n o) α x (Sum.inl.{u3, u4} n o)) B) (Matrix.vecMul.{u5, u4, u2} o m α _inst_3 _inst_2 (Function.comp.{succ u4, max (succ u3) (succ u4), succ u5} o (Sum.{u3, u4} n o) α x (Sum.inr.{u3, u4} n o)) D)))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u1}} {n : Type.{u5}} {o : Type.{u4}} {α : Type.{u3}} [_inst_1 : Fintype.{u5} n] [_inst_2 : Fintype.{u4} o] [_inst_3 : NonUnitalNonAssocSemiring.{u3} α] (A : Matrix.{u5, u2, u3} n l α) (B : Matrix.{u5, u1, u3} n m α) (C : Matrix.{u4, u2, u3} o l α) (D : Matrix.{u4, u1, u3} o m α) (x : (Sum.{u5, u4} n o) -> α), Eq.{max (max (succ u2) (succ u1)) (succ u3)} ((Sum.{u2, u1} l m) -> α) (Matrix.vecMul.{u3, max u5 u4, max u1 u2} (Sum.{u5, u4} n o) (Sum.{u2, u1} l m) α _inst_3 (instFintypeSum.{u5, u4} n o _inst_1 _inst_2) x (Matrix.fromBlocks.{u2, u1, u5, u4, u3} l m n o α A B C D)) (Sum.elim.{u2, u1, succ u3} l m α (HAdd.hAdd.{max u2 u3, max u2 u3, max u2 u3} (l -> α) (l -> α) (l -> α) (instHAdd.{max u2 u3} (l -> α) (Pi.instAdd.{u2, u3} l (fun (ᾰ : l) => α) (fun (i : l) => Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3)))) (Matrix.vecMul.{u3, u5, u2} n l α _inst_3 _inst_1 (Function.comp.{succ u5, max (succ u5) (succ u4), succ u3} n (Sum.{u5, u4} n o) α x (Sum.inl.{u5, u4} n o)) A) (Matrix.vecMul.{u3, u4, u2} o l α _inst_3 _inst_2 (Function.comp.{succ u4, max (succ u5) (succ u4), succ u3} o (Sum.{u5, u4} n o) α x (Sum.inr.{u5, u4} n o)) C)) (HAdd.hAdd.{max u1 u3, max u1 u3, max u1 u3} (m -> α) (m -> α) (m -> α) (instHAdd.{max u1 u3} (m -> α) (Pi.instAdd.{u1, u3} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3)))) (Matrix.vecMul.{u3, u5, u1} n m α _inst_3 _inst_1 (Function.comp.{succ u5, max (succ u5) (succ u4), succ u3} n (Sum.{u5, u4} n o) α x (Sum.inl.{u5, u4} n o)) B) (Matrix.vecMul.{u3, u4, u1} o m α _inst_3 _inst_2 (Function.comp.{succ u4, max (succ u5) (succ u4), succ u3} o (Sum.{u5, u4} n o) α x (Sum.inr.{u5, u4} n o)) D)))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_from_blocks Matrix.vecMul_fromBlocksₓ'. -/
theorem vecMul_fromBlocks [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : Sum n o → α) :
    vecMul x (fromBlocks A B C D) =
      Sum.elim (vecMul (x ∘ Sum.inl) A + vecMul (x ∘ Sum.inr) C)
        (vecMul (x ∘ Sum.inl) B + vecMul (x ∘ Sum.inr) D) :=
  by ext i; cases i <;> simp [vec_mul, dot_product]
#align matrix.vec_mul_from_blocks Matrix.vecMul_fromBlocks

variable [DecidableEq l] [DecidableEq m]

section Zero

variable [Zero α]

/- warning: matrix.to_block_diagonal_self -> Matrix.toBlock_diagonal_self is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : Zero.{u2} α] (d : m -> α) (p : m -> Prop), Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => p a)) α) (Matrix.toBlock.{u1, u1, u2} m m α (Matrix.diagonal.{u2, u1} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 d) p p) (Matrix.diagonal.{u2, u1} (Subtype.{succ u1} m (fun (a : m) => p a)) α (fun (a : Subtype.{succ u1} m (fun (a : m) => p a)) (b : Subtype.{succ u1} m (fun (a : m) => p a)) => Subtype.decidableEq.{u1} m (fun (x : m) => p x) (fun (a : m) (b : m) => _inst_2 a b) a b) _inst_3 (fun (i : Subtype.{succ u1} m p) => d ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} m p) m (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} m p) m (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} m p) m (coeBase.{succ u1, succ u1} (Subtype.{succ u1} m p) m (coeSubtype.{succ u1} m (fun (x : m) => p x))))) i)))
but is expected to have type
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : Zero.{u1} α] (d : m -> α) (p : m -> Prop), Eq.{max (succ u2) (succ u1)} (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => p a)) α) (Matrix.toBlock.{u2, u2, u1} m m α (Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 d) p p) (Matrix.diagonal.{u1, u2} (Subtype.{succ u2} m p) α (fun (a : Subtype.{succ u2} m p) (b : Subtype.{succ u2} m p) => Subtype.instDecidableEqSubtype.{u2} m (fun (x : m) => p x) (fun (a : m) (b : m) => _inst_2 a b) a b) _inst_3 (fun (i : Subtype.{succ u2} m p) => d (Subtype.val.{succ u2} m p i)))
Case conversion may be inaccurate. Consider using '#align matrix.to_block_diagonal_self Matrix.toBlock_diagonal_selfₓ'. -/
theorem toBlock_diagonal_self (d : m → α) (p : m → Prop) :
    Matrix.toBlock (diagonal d) p p = diagonal fun i : Subtype p => d ↑i :=
  by
  ext (i j)
  by_cases i = j
  · simp [h]
  · simp [One.one, h, fun h' => h <| Subtype.ext h']
#align matrix.to_block_diagonal_self Matrix.toBlock_diagonal_self

/- warning: matrix.to_block_diagonal_disjoint -> Matrix.toBlock_diagonal_disjoint is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : Zero.{u2} α] (d : m -> α) {p : m -> Prop} {q : m -> Prop}, (Disjoint.{u1} (m -> Prop) (Pi.partialOrder.{u1, 0} m (fun (ᾰ : m) => Prop) (fun (i : m) => Prop.partialOrder)) (Pi.orderBot.{u1, 0} m (fun (ᾰ : m) => Prop) (fun (i : m) => Preorder.toHasLe.{0} ((fun (i : m) => (fun (i : m) => (fun (ᾰ : m) => Prop) i) i) i) ((fun (i : m) => PartialOrder.toPreorder.{0} ((fun (ᾰ : m) => Prop) i) ((fun (i : m) => Prop.partialOrder) i)) i)) (fun (i : m) => BoundedOrder.toOrderBot.{0} Prop (Preorder.toHasLe.{0} ((fun (i : m) => (fun (i : m) => (fun (ᾰ : m) => Prop) i) i) i) ((fun (i : m) => PartialOrder.toPreorder.{0} ((fun (ᾰ : m) => Prop) i) ((fun (i : m) => Prop.partialOrder) i)) i)) Prop.boundedOrder)) p q) -> (Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => q a)) α) (Matrix.toBlock.{u1, u1, u2} m m α (Matrix.diagonal.{u2, u1} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 d) p q) (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => q a)) α) 0 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => q a)) α) 0 (Zero.zero.{max u1 u2} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => q a)) α) (Matrix.hasZero.{u2, u1, u1} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => q a)) α _inst_3)))))
but is expected to have type
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : Zero.{u1} α] (d : m -> α) {p : m -> Prop} {q : m -> Prop}, (Disjoint.{u2} (m -> Prop) (Pi.partialOrder.{u2, 0} m (fun (ᾰ : m) => Prop) (fun (i : m) => Prop.partialOrder)) (Pi.orderBot.{u2, 0} m (fun (ᾰ : m) => Prop) (fun (i : m) => Preorder.toLE.{0} ((fun (i : m) => (fun (i : m) => Prop) i) i) ((fun (i : m) => PartialOrder.toPreorder.{0} ((fun (ᾰ : m) => Prop) i) ((fun (i : m) => Prop.partialOrder) i)) i)) (fun (i : m) => BoundedOrder.toOrderBot.{0} Prop Prop.le Prop.boundedOrder)) p q) -> (Eq.{max (succ u2) (succ u1)} (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => q a)) α) (Matrix.toBlock.{u2, u2, u1} m m α (Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 d) p q) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => q a)) α) 0 (Zero.toOfNat0.{max u2 u1} (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => q a)) α) (Matrix.zero.{u1, u2, u2} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => q a)) α _inst_3))))
Case conversion may be inaccurate. Consider using '#align matrix.to_block_diagonal_disjoint Matrix.toBlock_diagonal_disjointₓ'. -/
theorem toBlock_diagonal_disjoint (d : m → α) {p q : m → Prop} (hpq : Disjoint p q) :
    Matrix.toBlock (diagonal d) p q = 0 :=
  by
  ext (⟨i, hi⟩⟨j, hj⟩)
  have : i ≠ j := fun heq => hpq.le_bot i ⟨hi, HEq.symm ▸ hj⟩
  simp [diagonal_apply_ne d this]
#align matrix.to_block_diagonal_disjoint Matrix.toBlock_diagonal_disjoint

/- warning: matrix.from_blocks_diagonal -> Matrix.fromBlocks_diagonal is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} l] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : Zero.{u3} α] (d₁ : l -> α) (d₂ : m -> α), Eq.{succ (max (max u1 u2) u3)} (Matrix.{max u1 u2, max u1 u2, u3} (Sum.{u1, u2} l m) (Sum.{u1, u2} l m) α) (Matrix.fromBlocks.{u1, u2, u1, u2, u3} l m l m α (Matrix.diagonal.{u3, u1} l α (fun (a : l) (b : l) => _inst_1 a b) _inst_3 d₁) (OfNat.ofNat.{max u1 u2 u3} (Matrix.{u1, u2, u3} l m α) 0 (OfNat.mk.{max u1 u2 u3} (Matrix.{u1, u2, u3} l m α) 0 (Zero.zero.{max u1 u2 u3} (Matrix.{u1, u2, u3} l m α) (Matrix.hasZero.{u3, u1, u2} l m α _inst_3)))) (OfNat.ofNat.{max u2 u1 u3} (Matrix.{u2, u1, u3} m l α) 0 (OfNat.mk.{max u2 u1 u3} (Matrix.{u2, u1, u3} m l α) 0 (Zero.zero.{max u2 u1 u3} (Matrix.{u2, u1, u3} m l α) (Matrix.hasZero.{u3, u2, u1} m l α _inst_3)))) (Matrix.diagonal.{u3, u2} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 d₂)) (Matrix.diagonal.{u3, max u1 u2} (Sum.{u1, u2} l m) α (fun (a : Sum.{u1, u2} l m) (b : Sum.{u1, u2} l m) => Sum.decidableEq.{u1, u2} l (fun (a : l) (b : l) => _inst_1 a b) m (fun (a : m) (b : m) => _inst_2 a b) a b) _inst_3 (Sum.elim.{u1, u2, succ u3} l m α d₁ d₂))
but is expected to have type
  forall {l : Type.{u3}} {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} l] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : Zero.{u1} α] (d₁ : l -> α) (d₂ : m -> α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{max u2 u3, max u2 u3, u1} (Sum.{u3, u2} l m) (Sum.{u3, u2} l m) α) (Matrix.fromBlocks.{u3, u2, u3, u2, u1} l m l m α (Matrix.diagonal.{u1, u3} l α (fun (a : l) (b : l) => _inst_1 a b) _inst_3 d₁) (OfNat.ofNat.{max (max u3 u1) u2} (Matrix.{u3, u2, u1} l m α) 0 (Zero.toOfNat0.{max (max u3 u1) u2} (Matrix.{u3, u2, u1} l m α) (Matrix.zero.{u1, u3, u2} l m α _inst_3))) (OfNat.ofNat.{max (max u3 u1) u2} (Matrix.{u2, u3, u1} m l α) 0 (Zero.toOfNat0.{max (max u3 u1) u2} (Matrix.{u2, u3, u1} m l α) (Matrix.zero.{u1, u2, u3} m l α _inst_3))) (Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 d₂)) (Matrix.diagonal.{u1, max u2 u3} (Sum.{u3, u2} l m) α (fun (a : Sum.{u3, u2} l m) (b : Sum.{u3, u2} l m) => Sum.instDecidableEqSum.{u3, u2} l m (fun (a : l) (b : l) => _inst_1 a b) (fun (a : m) (b : m) => _inst_2 a b) a b) _inst_3 (Sum.elim.{u3, u2, succ u1} l m α d₁ d₂))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_diagonal Matrix.fromBlocks_diagonalₓ'. -/
@[simp]
theorem fromBlocks_diagonal (d₁ : l → α) (d₂ : m → α) :
    fromBlocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (Sum.elim d₁ d₂) := by ext (i j);
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [diagonal]
#align matrix.from_blocks_diagonal Matrix.fromBlocks_diagonal

end Zero

section HasZeroHasOne

variable [Zero α] [One α]

/- warning: matrix.from_blocks_one -> Matrix.fromBlocks_one is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u1}} {m : Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} l] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : Zero.{u3} α] [_inst_4 : One.{u3} α], Eq.{succ (max (max u1 u2) u3)} (Matrix.{max u1 u2, max u1 u2, u3} (Sum.{u1, u2} l m) (Sum.{u1, u2} l m) α) (Matrix.fromBlocks.{u1, u2, u1, u2, u3} l m l m α (OfNat.ofNat.{max u1 u3} (Matrix.{u1, u1, u3} l l α) 1 (OfNat.mk.{max u1 u3} (Matrix.{u1, u1, u3} l l α) 1 (One.one.{max u1 u3} (Matrix.{u1, u1, u3} l l α) (Matrix.hasOne.{u3, u1} l α (fun (a : l) (b : l) => _inst_1 a b) _inst_3 _inst_4)))) (OfNat.ofNat.{max u1 u2 u3} (Matrix.{u1, u2, u3} l m α) 0 (OfNat.mk.{max u1 u2 u3} (Matrix.{u1, u2, u3} l m α) 0 (Zero.zero.{max u1 u2 u3} (Matrix.{u1, u2, u3} l m α) (Matrix.hasZero.{u3, u1, u2} l m α _inst_3)))) (OfNat.ofNat.{max u2 u1 u3} (Matrix.{u2, u1, u3} m l α) 0 (OfNat.mk.{max u2 u1 u3} (Matrix.{u2, u1, u3} m l α) 0 (Zero.zero.{max u2 u1 u3} (Matrix.{u2, u1, u3} m l α) (Matrix.hasZero.{u3, u2, u1} m l α _inst_3)))) (OfNat.ofNat.{max u2 u3} (Matrix.{u2, u2, u3} m m α) 1 (OfNat.mk.{max u2 u3} (Matrix.{u2, u2, u3} m m α) 1 (One.one.{max u2 u3} (Matrix.{u2, u2, u3} m m α) (Matrix.hasOne.{u3, u2} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4))))) (OfNat.ofNat.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Sum.{u1, u2} l m) (Sum.{u1, u2} l m) α) 1 (OfNat.mk.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Sum.{u1, u2} l m) (Sum.{u1, u2} l m) α) 1 (One.one.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Sum.{u1, u2} l m) (Sum.{u1, u2} l m) α) (Matrix.hasOne.{u3, max u1 u2} (Sum.{u1, u2} l m) α (fun (a : Sum.{u1, u2} l m) (b : Sum.{u1, u2} l m) => Sum.decidableEq.{u1, u2} l (fun (a : l) (b : l) => _inst_1 a b) m (fun (a : m) (b : m) => _inst_2 a b) a b) _inst_3 _inst_4))))
but is expected to have type
  forall {l : Type.{u3}} {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} l] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : Zero.{u1} α] [_inst_4 : One.{u1} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{max u2 u3, max u2 u3, u1} (Sum.{u3, u2} l m) (Sum.{u3, u2} l m) α) (Matrix.fromBlocks.{u3, u2, u3, u2, u1} l m l m α (OfNat.ofNat.{max u3 u1} (Matrix.{u3, u3, u1} l l α) 1 (One.toOfNat1.{max u3 u1} (Matrix.{u3, u3, u1} l l α) (Matrix.one.{u1, u3} l α (fun (a : l) (b : l) => _inst_1 a b) _inst_3 _inst_4))) (OfNat.ofNat.{max (max u3 u1) u2} (Matrix.{u3, u2, u1} l m α) 0 (Zero.toOfNat0.{max (max u3 u1) u2} (Matrix.{u3, u2, u1} l m α) (Matrix.zero.{u1, u3, u2} l m α _inst_3))) (OfNat.ofNat.{max (max u3 u1) u2} (Matrix.{u2, u3, u1} m l α) 0 (Zero.toOfNat0.{max (max u3 u1) u2} (Matrix.{u2, u3, u1} m l α) (Matrix.zero.{u1, u2, u3} m l α _inst_3))) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} m m α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.one.{u1, u2} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4)))) (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{max u2 u3, max u2 u3, u1} (Sum.{u3, u2} l m) (Sum.{u3, u2} l m) α) 1 (One.toOfNat1.{max (max u3 u2) u1} (Matrix.{max u2 u3, max u2 u3, u1} (Sum.{u3, u2} l m) (Sum.{u3, u2} l m) α) (Matrix.one.{u1, max u3 u2} (Sum.{u3, u2} l m) α (fun (a : Sum.{u3, u2} l m) (b : Sum.{u3, u2} l m) => Sum.instDecidableEqSum.{u3, u2} l m (fun (a : l) (b : l) => _inst_1 a b) (fun (a : m) (b : m) => _inst_2 a b) a b) _inst_3 _inst_4)))
Case conversion may be inaccurate. Consider using '#align matrix.from_blocks_one Matrix.fromBlocks_oneₓ'. -/
@[simp]
theorem fromBlocks_one : fromBlocks (1 : Matrix l l α) 0 0 (1 : Matrix m m α) = 1 := by ext (i j);
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [one_apply]
#align matrix.from_blocks_one Matrix.fromBlocks_one

/- warning: matrix.to_block_one_self -> Matrix.toBlock_one_self is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : Zero.{u2} α] [_inst_4 : One.{u2} α] (p : m -> Prop), Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => p a)) α) (Matrix.toBlock.{u1, u1, u2} m m α (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} m m α) 1 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} m m α) 1 (One.one.{max u1 u2} (Matrix.{u1, u1, u2} m m α) (Matrix.hasOne.{u2, u1} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4)))) p p) (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => p a)) α) 1 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => p a)) α) 1 (One.one.{max u1 u2} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => p a)) α) (Matrix.hasOne.{u2, u1} (Subtype.{succ u1} m (fun (a : m) => p a)) α (fun (a : Subtype.{succ u1} m (fun (a : m) => p a)) (b : Subtype.{succ u1} m (fun (a : m) => p a)) => Subtype.decidableEq.{u1} m (fun (x : m) => p x) (fun (a : m) (b : m) => _inst_2 a b) a b) _inst_3 _inst_4))))
but is expected to have type
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : Zero.{u1} α] [_inst_4 : One.{u1} α] (p : m -> Prop), Eq.{max (succ u2) (succ u1)} (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => p a)) α) (Matrix.toBlock.{u2, u2, u1} m m α (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} m m α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.one.{u1, u2} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4))) p p) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => p a)) α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => p a)) α) (Matrix.one.{u1, u2} (Subtype.{succ u2} m (fun (a : m) => p a)) α (fun (a : Subtype.{succ u2} m (fun (a : m) => p a)) (b : Subtype.{succ u2} m (fun (a : m) => p a)) => Subtype.instDecidableEqSubtype.{u2} m (fun (x : m) => p x) (fun (a : m) (b : m) => _inst_2 a b) a b) _inst_3 _inst_4)))
Case conversion may be inaccurate. Consider using '#align matrix.to_block_one_self Matrix.toBlock_one_selfₓ'. -/
@[simp]
theorem toBlock_one_self (p : m → Prop) : Matrix.toBlock (1 : Matrix m m α) p p = 1 :=
  toBlock_diagonal_self _ p
#align matrix.to_block_one_self Matrix.toBlock_one_self

/- warning: matrix.to_block_one_disjoint -> Matrix.toBlock_one_disjoint is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : Zero.{u2} α] [_inst_4 : One.{u2} α] {p : m -> Prop} {q : m -> Prop}, (Disjoint.{u1} (m -> Prop) (Pi.partialOrder.{u1, 0} m (fun (ᾰ : m) => Prop) (fun (i : m) => Prop.partialOrder)) (Pi.orderBot.{u1, 0} m (fun (ᾰ : m) => Prop) (fun (i : m) => Preorder.toHasLe.{0} ((fun (i : m) => (fun (i : m) => (fun (ᾰ : m) => Prop) i) i) i) ((fun (i : m) => PartialOrder.toPreorder.{0} ((fun (ᾰ : m) => Prop) i) ((fun (i : m) => Prop.partialOrder) i)) i)) (fun (i : m) => BoundedOrder.toOrderBot.{0} Prop (Preorder.toHasLe.{0} ((fun (i : m) => (fun (i : m) => (fun (ᾰ : m) => Prop) i) i) i) ((fun (i : m) => PartialOrder.toPreorder.{0} ((fun (ᾰ : m) => Prop) i) ((fun (i : m) => Prop.partialOrder) i)) i)) Prop.boundedOrder)) p q) -> (Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => q a)) α) (Matrix.toBlock.{u1, u1, u2} m m α (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} m m α) 1 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} m m α) 1 (One.one.{max u1 u2} (Matrix.{u1, u1, u2} m m α) (Matrix.hasOne.{u2, u1} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4)))) p q) (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => q a)) α) 0 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => q a)) α) 0 (Zero.zero.{max u1 u2} (Matrix.{u1, u1, u2} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => q a)) α) (Matrix.hasZero.{u2, u1, u1} (Subtype.{succ u1} m (fun (a : m) => p a)) (Subtype.{succ u1} m (fun (a : m) => q a)) α _inst_3)))))
but is expected to have type
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : Zero.{u1} α] [_inst_4 : One.{u1} α] {p : m -> Prop} {q : m -> Prop}, (Disjoint.{u2} (m -> Prop) (Pi.partialOrder.{u2, 0} m (fun (ᾰ : m) => Prop) (fun (i : m) => Prop.partialOrder)) (Pi.orderBot.{u2, 0} m (fun (ᾰ : m) => Prop) (fun (i : m) => Preorder.toLE.{0} ((fun (i : m) => (fun (i : m) => Prop) i) i) ((fun (i : m) => PartialOrder.toPreorder.{0} ((fun (ᾰ : m) => Prop) i) ((fun (i : m) => Prop.partialOrder) i)) i)) (fun (i : m) => BoundedOrder.toOrderBot.{0} Prop Prop.le Prop.boundedOrder)) p q) -> (Eq.{max (succ u2) (succ u1)} (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => q a)) α) (Matrix.toBlock.{u2, u2, u1} m m α (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} m m α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.one.{u1, u2} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4))) p q) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => q a)) α) 0 (Zero.toOfNat0.{max u2 u1} (Matrix.{u2, u2, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => q a)) α) (Matrix.zero.{u1, u2, u2} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u2} m (fun (a : m) => q a)) α _inst_3))))
Case conversion may be inaccurate. Consider using '#align matrix.to_block_one_disjoint Matrix.toBlock_one_disjointₓ'. -/
theorem toBlock_one_disjoint {p q : m → Prop} (hpq : Disjoint p q) :
    Matrix.toBlock (1 : Matrix m m α) p q = 0 :=
  toBlock_diagonal_disjoint _ hpq
#align matrix.to_block_one_disjoint Matrix.toBlock_one_disjoint

end HasZeroHasOne

end BlockMatrices

section BlockDiagonal

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

#print Matrix.blockDiagonal /-
/-- `matrix.block_diagonal M` turns a homogenously-indexed collection of matrices
`M : o → matrix m n α'` into a `m × o`-by-`n × o` block matrix which has the entries of `M` along
the diagonal and zero elsewhere.

See also `matrix.block_diagonal'` if the matrices may not have the same size everywhere.
-/
def blockDiagonal (M : o → Matrix m n α) : Matrix (m × o) (n × o) α :=
  of <| (fun ⟨i, k⟩ ⟨j, k'⟩ => if k = k' then M k i j else 0 : m × o → n × o → α)
#align matrix.block_diagonal Matrix.blockDiagonal
-/

/- warning: matrix.block_diagonal_apply' -> Matrix.blockDiagonal_apply' is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : Zero.{u4} α] (M : o -> (Matrix.{u1, u2, u4} m n α)) (i : m) (k : o) (j : n) (k' : o), Eq.{succ u4} α (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Prod.mk.{u1, u3} m o i k) (Prod.mk.{u2, u3} n o j k')) (ite.{succ u4} α (Eq.{succ u3} o k k') (_inst_1 k k') (M k i j) (OfNat.ofNat.{u4} α 0 (OfNat.mk.{u4} α 0 (Zero.zero.{u4} α _inst_2))))
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : o -> (Matrix.{u4, u3, u2} m n α)) (i : m) (k : o) (j : n) (k' : o), Eq.{succ u2} α (Matrix.blockDiagonal.{u4, u3, u1, u2} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Prod.mk.{u4, u1} m o i k) (Prod.mk.{u3, u1} n o j k')) (ite.{succ u2} α (Eq.{succ u1} o k k') (_inst_1 k k') (M k i j) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_apply' Matrix.blockDiagonal_apply'ₓ'. -/
-- TODO: set as an equation lemma for `block_diagonal`, see mathlib4#3024
theorem blockDiagonal_apply' (M : o → Matrix m n α) (i k j k') :
    blockDiagonal M ⟨i, k⟩ ⟨j, k'⟩ = if k = k' then M k i j else 0 :=
  rfl
#align matrix.block_diagonal_apply' Matrix.blockDiagonal_apply'

/- warning: matrix.block_diagonal_apply -> Matrix.blockDiagonal_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : Zero.{u4} α] (M : o -> (Matrix.{u1, u2, u4} m n α)) (ik : Prod.{u1, u3} m o) (jk : Prod.{u2, u3} n o), Eq.{succ u4} α (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M ik jk) (ite.{succ u4} α (Eq.{succ u3} o (Prod.snd.{u1, u3} m o ik) (Prod.snd.{u2, u3} n o jk)) (_inst_1 (Prod.snd.{u1, u3} m o ik) (Prod.snd.{u2, u3} n o jk)) (M (Prod.snd.{u1, u3} m o ik) (Prod.fst.{u1, u3} m o ik) (Prod.fst.{u2, u3} n o jk)) (OfNat.ofNat.{u4} α 0 (OfNat.mk.{u4} α 0 (Zero.zero.{u4} α _inst_2))))
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : o -> (Matrix.{u4, u3, u2} m n α)) (ik : Prod.{u4, u1} m o) (jk : Prod.{u3, u1} n o), Eq.{succ u2} α (Matrix.blockDiagonal.{u4, u3, u1, u2} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M ik jk) (ite.{succ u2} α (Eq.{succ u1} o (Prod.snd.{u4, u1} m o ik) (Prod.snd.{u3, u1} n o jk)) (_inst_1 (Prod.snd.{u4, u1} m o ik) (Prod.snd.{u3, u1} n o jk)) (M (Prod.snd.{u4, u1} m o ik) (Prod.fst.{u4, u1} m o ik) (Prod.fst.{u3, u1} n o jk)) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_apply Matrix.blockDiagonal_applyₓ'. -/
theorem blockDiagonal_apply (M : o → Matrix m n α) (ik jk) :
    blockDiagonal M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0 := by cases ik; cases jk;
  rfl
#align matrix.block_diagonal_apply Matrix.blockDiagonal_apply

/- warning: matrix.block_diagonal_apply_eq -> Matrix.blockDiagonal_apply_eq is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : Zero.{u4} α] (M : o -> (Matrix.{u1, u2, u4} m n α)) (i : m) (j : n) (k : o), Eq.{succ u4} α (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Prod.mk.{u1, u3} m o i k) (Prod.mk.{u2, u3} n o j k)) (M k i j)
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : o -> (Matrix.{u4, u3, u2} m n α)) (i : m) (j : n) (k : o), Eq.{succ u2} α (Matrix.blockDiagonal.{u4, u3, u1, u2} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Prod.mk.{u4, u1} m o i k) (Prod.mk.{u3, u1} n o j k)) (M k i j)
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_apply_eq Matrix.blockDiagonal_apply_eqₓ'. -/
@[simp]
theorem blockDiagonal_apply_eq (M : o → Matrix m n α) (i j k) :
    blockDiagonal M (i, k) (j, k) = M k i j :=
  if_pos rfl
#align matrix.block_diagonal_apply_eq Matrix.blockDiagonal_apply_eq

/- warning: matrix.block_diagonal_apply_ne -> Matrix.blockDiagonal_apply_ne is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : Zero.{u4} α] (M : o -> (Matrix.{u1, u2, u4} m n α)) (i : m) (j : n) {k : o} {k' : o}, (Ne.{succ u3} o k k') -> (Eq.{succ u4} α (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Prod.mk.{u1, u3} m o i k) (Prod.mk.{u2, u3} n o j k')) (OfNat.ofNat.{u4} α 0 (OfNat.mk.{u4} α 0 (Zero.zero.{u4} α _inst_2))))
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : o -> (Matrix.{u4, u3, u2} m n α)) (i : m) (j : n) {k : o} {k' : o}, (Ne.{succ u1} o k k') -> (Eq.{succ u2} α (Matrix.blockDiagonal.{u4, u3, u1, u2} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Prod.mk.{u4, u1} m o i k) (Prod.mk.{u3, u1} n o j k')) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_apply_ne Matrix.blockDiagonal_apply_neₓ'. -/
theorem blockDiagonal_apply_ne (M : o → Matrix m n α) (i j) {k k'} (h : k ≠ k') :
    blockDiagonal M (i, k) (j, k') = 0 :=
  if_neg h
#align matrix.block_diagonal_apply_ne Matrix.blockDiagonal_apply_ne

/- warning: matrix.block_diagonal_map -> Matrix.blockDiagonal_map is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} {β : Type.{u5}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : Zero.{u4} α] [_inst_3 : Zero.{u5} β] (M : o -> (Matrix.{u1, u2, u4} m n α)) (f : α -> β), (Eq.{succ u5} β (f (OfNat.ofNat.{u4} α 0 (OfNat.mk.{u4} α 0 (Zero.zero.{u4} α _inst_2)))) (OfNat.ofNat.{u5} β 0 (OfNat.mk.{u5} β 0 (Zero.zero.{u5} β _inst_3)))) -> (Eq.{succ (max (max u1 u3) (max u2 u3) u5)} (Matrix.{max u1 u3, max u2 u3, u5} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) β) (Matrix.map.{u4, u5, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α β (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M) f) (Matrix.blockDiagonal.{u1, u2, u3, u5} m n o β (fun (a : o) (b : o) => _inst_1 a b) _inst_3 (fun (k : o) => Matrix.map.{u4, u5, u1, u2} m n α β (M k) f)))
but is expected to have type
  forall {m : Type.{u5}} {n : Type.{u4}} {o : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u3} α] [_inst_3 : Zero.{u2} β] (M : o -> (Matrix.{u5, u4, u3} m n α)) (f : α -> β), (Eq.{succ u2} β (f (OfNat.ofNat.{u3} α 0 (Zero.toOfNat0.{u3} α _inst_2))) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_3))) -> (Eq.{max (max (max (succ u5) (succ u4)) (succ u1)) (succ u2)} (Matrix.{max u5 u1, max u4 u1, u2} (Prod.{u5, u1} m o) (Prod.{u4, u1} n o) β) (Matrix.map.{u3, u2, max u5 u1, max u4 u1} (Prod.{u5, u1} m o) (Prod.{u4, u1} n o) α β (Matrix.blockDiagonal.{u5, u4, u1, u3} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M) f) (Matrix.blockDiagonal.{u5, u4, u1, u2} m n o β (fun (a : o) (b : o) => _inst_1 a b) _inst_3 (fun (k : o) => Matrix.map.{u3, u2, u5, u4} m n α β (M k) f)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_map Matrix.blockDiagonal_mapₓ'. -/
theorem blockDiagonal_map (M : o → Matrix m n α) (f : α → β) (hf : f 0 = 0) :
    (blockDiagonal M).map f = blockDiagonal fun k => (M k).map f :=
  by
  ext
  simp only [map_apply, block_diagonal_apply, eq_comm]
  rw [apply_ite f, hf]
#align matrix.block_diagonal_map Matrix.blockDiagonal_map

/- warning: matrix.block_diagonal_transpose -> Matrix.blockDiagonal_transpose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : Zero.{u4} α] (M : o -> (Matrix.{u1, u2, u4} m n α)), Eq.{succ (max (max u2 u3) (max u1 u3) u4)} (Matrix.{max u2 u3, max u1 u3, u4} (Prod.{u2, u3} n o) (Prod.{u1, u3} m o) α) (Matrix.transpose.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M)) (Matrix.blockDiagonal.{u2, u1, u3, u4} n m o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (fun (k : o) => Matrix.transpose.{u4, u1, u2} m n α (M k)))
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : o -> (Matrix.{u4, u3, u2} m n α)), Eq.{max (max (max (succ u4) (succ u3)) (succ u1)) (succ u2)} (Matrix.{max u1 u3, max u1 u4, u2} (Prod.{u3, u1} n o) (Prod.{u4, u1} m o) α) (Matrix.transpose.{u2, max u1 u4, max u1 u3} (Prod.{u4, u1} m o) (Prod.{u3, u1} n o) α (Matrix.blockDiagonal.{u4, u3, u1, u2} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M)) (Matrix.blockDiagonal.{u3, u4, u1, u2} n m o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (fun (k : o) => Matrix.transpose.{u2, u4, u3} m n α (M k)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_transpose Matrix.blockDiagonal_transposeₓ'. -/
@[simp]
theorem blockDiagonal_transpose (M : o → Matrix m n α) :
    (blockDiagonal M)ᵀ = blockDiagonal fun k => (M k)ᵀ :=
  by
  ext
  simp only [transpose_apply, block_diagonal_apply, eq_comm]
  split_ifs with h
  · rw [h]
  · rfl
#align matrix.block_diagonal_transpose Matrix.blockDiagonal_transpose

/- warning: matrix.block_diagonal_conj_transpose -> Matrix.blockDiagonal_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} [_inst_1 : DecidableEq.{succ u3} o] {α : Type.{u4}} [_inst_4 : AddMonoid.{u4} α] [_inst_5 : StarAddMonoid.{u4} α _inst_4] (M : o -> (Matrix.{u1, u2, u4} m n α)), Eq.{succ (max (max u2 u3) (max u1 u3) u4)} (Matrix.{max u2 u3, max u1 u3, u4} (Prod.{u2, u3} n o) (Prod.{u1, u3} m o) α) (Matrix.conjTranspose.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α (InvolutiveStar.toHasStar.{u4} α (StarAddMonoid.toHasInvolutiveStar.{u4} α _inst_4 _inst_5)) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_4)) M)) (Matrix.blockDiagonal.{u2, u1, u3, u4} n m o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_4)) (fun (k : o) => Matrix.conjTranspose.{u4, u1, u2} m n α (InvolutiveStar.toHasStar.{u4} α (StarAddMonoid.toHasInvolutiveStar.{u4} α _inst_4 _inst_5)) (M k)))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} o] {α : Type.{u4}} [_inst_4 : AddMonoid.{u4} α] [_inst_5 : StarAddMonoid.{u4} α _inst_4] (M : o -> (Matrix.{u3, u2, u4} m n α)), Eq.{max (max (max (succ u3) (succ u2)) (succ u1)) (succ u4)} (Matrix.{max u1 u2, max u1 u3, u4} (Prod.{u2, u1} n o) (Prod.{u3, u1} m o) α) (Matrix.conjTranspose.{u4, max u1 u3, max u1 u2} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α _inst_4 _inst_5)) (Matrix.blockDiagonal.{u3, u2, u1, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddMonoid.toZero.{u4} α _inst_4) M)) (Matrix.blockDiagonal.{u2, u3, u1, u4} n m o α (fun (a : o) (b : o) => _inst_1 a b) (AddMonoid.toZero.{u4} α _inst_4) (fun (k : o) => Matrix.conjTranspose.{u4, u3, u2} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α _inst_4 _inst_5)) (M k)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_conj_transpose Matrix.blockDiagonal_conjTransposeₓ'. -/
@[simp]
theorem blockDiagonal_conjTranspose {α : Type _} [AddMonoid α] [StarAddMonoid α]
    (M : o → Matrix m n α) : (blockDiagonal M)ᴴ = blockDiagonal fun k => (M k)ᴴ :=
  by
  simp only [conj_transpose, block_diagonal_transpose]
  rw [block_diagonal_map _ star (star_zero α)]
#align matrix.block_diagonal_conj_transpose Matrix.blockDiagonal_conjTranspose

/- warning: matrix.block_diagonal_zero -> Matrix.blockDiagonal_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : Zero.{u4} α], Eq.{succ (max (max u1 u3) (max u2 u3) u4)} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (OfNat.ofNat.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) 0 (OfNat.mk.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) 0 (Zero.zero.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (Pi.instZero.{u3, max u1 u2 u4} o (fun (ᾰ : o) => Matrix.{u1, u2, u4} m n α) (fun (i : o) => Matrix.hasZero.{u4, u1, u2} m n α _inst_2)))))) (OfNat.ofNat.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) 0 (OfNat.mk.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) 0 (Zero.zero.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.hasZero.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α _inst_2))))
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} o] [_inst_2 : Zero.{u1} α], Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (Matrix.{max u2 u4, max u2 u3, u1} (Prod.{u4, u2} m o) (Prod.{u3, u2} n o) α) (Matrix.blockDiagonal.{u4, u3, u2, u1} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (OfNat.ofNat.{max (max (max u4 u3) u2) u1} (o -> (Matrix.{u4, u3, u1} m n α)) 0 (Zero.toOfNat0.{max (max (max u4 u3) u2) u1} (o -> (Matrix.{u4, u3, u1} m n α)) (Pi.instZero.{u2, max (max u4 u3) u1} o (fun (a._@.Mathlib.Data.Matrix.Block._hyg.4903 : o) => Matrix.{u4, u3, u1} m n α) (fun (i : o) => Matrix.zero.{u1, u4, u3} m n α _inst_2))))) (OfNat.ofNat.{max (max (max u4 u3) u2) u1} (Matrix.{max u2 u4, max u2 u3, u1} (Prod.{u4, u2} m o) (Prod.{u3, u2} n o) α) 0 (Zero.toOfNat0.{max (max (max u4 u3) u2) u1} (Matrix.{max u2 u4, max u2 u3, u1} (Prod.{u4, u2} m o) (Prod.{u3, u2} n o) α) (Matrix.zero.{u1, max u4 u2, max u3 u2} (Prod.{u4, u2} m o) (Prod.{u3, u2} n o) α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_zero Matrix.blockDiagonal_zeroₓ'. -/
@[simp]
theorem blockDiagonal_zero : blockDiagonal (0 : o → Matrix m n α) = 0 := by ext;
  simp [block_diagonal_apply]
#align matrix.block_diagonal_zero Matrix.blockDiagonal_zero

/- warning: matrix.block_diagonal_diagonal -> Matrix.blockDiagonal_diagonal is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {o : Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} o] [_inst_2 : Zero.{u3} α] [_inst_4 : DecidableEq.{succ u1} m] (d : o -> m -> α), Eq.{succ (max (max u1 u2) u3)} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) (Matrix.blockDiagonal.{u1, u1, u2, u3} m m o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (fun (k : o) => Matrix.diagonal.{u3, u1} m α (fun (a : m) (b : m) => _inst_4 a b) _inst_2 (d k))) (Matrix.diagonal.{u3, max u1 u2} (Prod.{u1, u2} m o) α (fun (a : Prod.{u1, u2} m o) (b : Prod.{u1, u2} m o) => Prod.decidableEq.{u1, u2} m o (fun (a : m) (b : m) => _inst_4 a b) (fun (a : o) (b : o) => _inst_1 a b) a b) _inst_2 (fun (ik : Prod.{u1, u2} m o) => d (Prod.snd.{u1, u2} m o ik) (Prod.fst.{u1, u2} m o ik)))
but is expected to have type
  forall {m : Type.{u3}} {o : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} o] [_inst_2 : Zero.{u1} α] [_inst_4 : DecidableEq.{succ u3} m] (d : o -> m -> α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{max u2 u3, max u2 u3, u1} (Prod.{u3, u2} m o) (Prod.{u3, u2} m o) α) (Matrix.blockDiagonal.{u3, u3, u2, u1} m m o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (fun (k : o) => Matrix.diagonal.{u1, u3} m α (fun (a : m) (b : m) => _inst_4 a b) _inst_2 (d k))) (Matrix.diagonal.{u1, max u3 u2} (Prod.{u3, u2} m o) α (fun (a : Prod.{u3, u2} m o) (b : Prod.{u3, u2} m o) => instDecidableEqProd.{u3, u2} m o (fun (a : m) (b : m) => _inst_4 a b) (fun (a : o) (b : o) => _inst_1 a b) a b) _inst_2 (fun (ik : Prod.{u3, u2} m o) => d (Prod.snd.{u3, u2} m o ik) (Prod.fst.{u3, u2} m o ik)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_diagonal Matrix.blockDiagonal_diagonalₓ'. -/
@[simp]
theorem blockDiagonal_diagonal [DecidableEq m] (d : o → m → α) :
    (blockDiagonal fun k => diagonal (d k)) = diagonal fun ik => d ik.2 ik.1 :=
  by
  ext (⟨i, k⟩⟨j, k'⟩)
  simp only [block_diagonal_apply, diagonal_apply, Prod.mk.inj_iff, ← ite_and]
  congr 1
  rw [and_comm']
#align matrix.block_diagonal_diagonal Matrix.blockDiagonal_diagonal

/- warning: matrix.block_diagonal_one -> Matrix.blockDiagonal_one is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {o : Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} o] [_inst_2 : Zero.{u3} α] [_inst_4 : DecidableEq.{succ u1} m] [_inst_5 : One.{u3} α], Eq.{succ (max (max u1 u2) u3)} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) (Matrix.blockDiagonal.{u1, u1, u2, u3} m m o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (OfNat.ofNat.{max u2 u1 u3} (o -> (Matrix.{u1, u1, u3} m m α)) 1 (OfNat.mk.{max u2 u1 u3} (o -> (Matrix.{u1, u1, u3} m m α)) 1 (One.one.{max u2 u1 u3} (o -> (Matrix.{u1, u1, u3} m m α)) (Pi.instOne.{u2, max u1 u3} o (fun (ᾰ : o) => Matrix.{u1, u1, u3} m m α) (fun (i : o) => Matrix.hasOne.{u3, u1} m α (fun (a : m) (b : m) => _inst_4 a b) _inst_2 _inst_5)))))) (OfNat.ofNat.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) 1 (OfNat.mk.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) 1 (One.one.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) (Matrix.hasOne.{u3, max u1 u2} (Prod.{u1, u2} m o) α (fun (a : Prod.{u1, u2} m o) (b : Prod.{u1, u2} m o) => Prod.decidableEq.{u1, u2} m o (fun (a : m) (b : m) => _inst_4 a b) (fun (a : o) (b : o) => _inst_1 a b) a b) _inst_2 _inst_5))))
but is expected to have type
  forall {m : Type.{u3}} {o : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] [_inst_4 : DecidableEq.{succ u3} m] [_inst_5 : One.{u2} α], Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{max u1 u3, max u1 u3, u2} (Prod.{u3, u1} m o) (Prod.{u3, u1} m o) α) (Matrix.blockDiagonal.{u3, u3, u1, u2} m m o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (OfNat.ofNat.{max (max u3 u1) u2} (o -> (Matrix.{u3, u3, u2} m m α)) 1 (One.toOfNat1.{max (max u3 u1) u2} (o -> (Matrix.{u3, u3, u2} m m α)) (Pi.instOne.{u1, max u3 u2} o (fun (a._@.Mathlib.Data.Matrix.Block._hyg.5056 : o) => Matrix.{u3, u3, u2} m m α) (fun (i : o) => Matrix.one.{u2, u3} m α (fun (a : m) (b : m) => _inst_4 a b) _inst_2 _inst_5))))) (OfNat.ofNat.{max (max u3 u1) u2} (Matrix.{max u1 u3, max u1 u3, u2} (Prod.{u3, u1} m o) (Prod.{u3, u1} m o) α) 1 (One.toOfNat1.{max (max u3 u1) u2} (Matrix.{max u1 u3, max u1 u3, u2} (Prod.{u3, u1} m o) (Prod.{u3, u1} m o) α) (Matrix.one.{u2, max u3 u1} (Prod.{u3, u1} m o) α (fun (a : Prod.{u3, u1} m o) (b : Prod.{u3, u1} m o) => instDecidableEqProd.{u3, u1} m o (fun (a : m) (b : m) => _inst_4 a b) (fun (a : o) (b : o) => _inst_1 a b) a b) _inst_2 _inst_5)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_one Matrix.blockDiagonal_oneₓ'. -/
@[simp]
theorem blockDiagonal_one [DecidableEq m] [One α] : blockDiagonal (1 : o → Matrix m m α) = 1 :=
  show (blockDiagonal fun _ : o => diagonal fun _ : m => (1 : α)) = diagonal fun _ => 1 by
    rw [block_diagonal_diagonal]
#align matrix.block_diagonal_one Matrix.blockDiagonal_one

end Zero

/- warning: matrix.block_diagonal_add -> Matrix.blockDiagonal_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : AddZeroClass.{u4} α] (M : o -> (Matrix.{u1, u2, u4} m n α)) (N : o -> (Matrix.{u1, u2, u4} m n α)), Eq.{succ (max (max u1 u3) (max u2 u3) u4)} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α _inst_2) (HAdd.hAdd.{max u3 u1 u2 u4, max u3 u1 u2 u4, max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (o -> (Matrix.{u1, u2, u4} m n α)) (o -> (Matrix.{u1, u2, u4} m n α)) (instHAdd.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (Pi.instAdd.{u3, max u1 u2 u4} o (fun (ᾰ : o) => Matrix.{u1, u2, u4} m n α) (fun (i : o) => Matrix.hasAdd.{u4, u1, u2} m n α (AddZeroClass.toHasAdd.{u4} α _inst_2)))) M N)) (HAdd.hAdd.{max (max u1 u3) (max u2 u3) u4, max (max u1 u3) (max u2 u3) u4, max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (instHAdd.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.hasAdd.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α (AddZeroClass.toHasAdd.{u4} α _inst_2))) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α _inst_2) M) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α _inst_2) N))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : AddZeroClass.{u4} α] (M : o -> (Matrix.{u3, u2, u4} m n α)) (N : o -> (Matrix.{u3, u2, u4} m n α)), Eq.{max (max (max (succ u3) (succ u2)) (succ u1)) (succ u4)} (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.blockDiagonal.{u3, u2, u1, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toZero.{u4} α _inst_2) (HAdd.hAdd.{max (max (max u3 u2) u1) u4, max (max (max u3 u2) u1) u4, max (max (max u3 u2) u1) u4} (o -> (Matrix.{u3, u2, u4} m n α)) (o -> (Matrix.{u3, u2, u4} m n α)) (o -> (Matrix.{u3, u2, u4} m n α)) (instHAdd.{max (max (max u3 u2) u1) u4} (o -> (Matrix.{u3, u2, u4} m n α)) (Pi.instAdd.{u1, max (max u3 u2) u4} o (fun (ᾰ : o) => Matrix.{u3, u2, u4} m n α) (fun (i : o) => Matrix.add.{u4, u3, u2} m n α (AddZeroClass.toAdd.{u4} α _inst_2)))) M N)) (HAdd.hAdd.{max (max (max u3 u2) u1) u4, max (max (max u3 u2) u1) u4, max (max (max u3 u2) u1) u4} (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (instHAdd.{max (max (max u3 u2) u1) u4} (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.add.{u4, max u3 u1, max u2 u1} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α (AddZeroClass.toAdd.{u4} α _inst_2))) (Matrix.blockDiagonal.{u3, u2, u1, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toZero.{u4} α _inst_2) M) (Matrix.blockDiagonal.{u3, u2, u1, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toZero.{u4} α _inst_2) N))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_add Matrix.blockDiagonal_addₓ'. -/
@[simp]
theorem blockDiagonal_add [AddZeroClass α] (M N : o → Matrix m n α) :
    blockDiagonal (M + N) = blockDiagonal M + blockDiagonal N :=
  by
  ext
  simp only [block_diagonal_apply, Pi.add_apply]
  split_ifs <;> simp
#align matrix.block_diagonal_add Matrix.blockDiagonal_add

section

variable (o m n α)

#print Matrix.blockDiagonalAddMonoidHom /-
/-- `matrix.block_diagonal` as an `add_monoid_hom`. -/
@[simps]
def blockDiagonalAddMonoidHom [AddZeroClass α] : (o → Matrix m n α) →+ Matrix (m × o) (n × o) α
    where
  toFun := blockDiagonal
  map_zero' := blockDiagonal_zero
  map_add' := blockDiagonal_add
#align matrix.block_diagonal_add_monoid_hom Matrix.blockDiagonalAddMonoidHom
-/

end

/- warning: matrix.block_diagonal_neg -> Matrix.blockDiagonal_neg is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : AddGroup.{u4} α] (M : o -> (Matrix.{u1, u2, u4} m n α)), Eq.{succ (max (max u1 u3) (max u2 u3) u4)} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) (Neg.neg.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (Pi.instNeg.{u3, max u1 u2 u4} o (fun (ᾰ : o) => Matrix.{u1, u2, u4} m n α) (fun (i : o) => Matrix.hasNeg.{u4, u1, u2} m n α (SubNegMonoid.toHasNeg.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) M)) (Neg.neg.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.hasNeg.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α (SubNegMonoid.toHasNeg.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2))) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) M))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : AddGroup.{u4} α] (M : o -> (Matrix.{u3, u2, u4} m n α)), Eq.{max (max (max (succ u3) (succ u2)) (succ u1)) (succ u4)} (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.blockDiagonal.{u3, u2, u1, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))) (Neg.neg.{max (max (max u3 u2) u1) u4} (o -> (Matrix.{u3, u2, u4} m n α)) (Pi.instNeg.{u1, max (max u3 u2) u4} o (fun (ᾰ : o) => Matrix.{u3, u2, u4} m n α) (fun (i : o) => Matrix.neg.{u4, u3, u2} m n α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))))) M)) (Neg.neg.{max (max (max u3 u2) u1) u4} (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.neg.{u4, max u3 u1, max u2 u1} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2))))) (Matrix.blockDiagonal.{u3, u2, u1, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))) M))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_neg Matrix.blockDiagonal_negₓ'. -/
@[simp]
theorem blockDiagonal_neg [AddGroup α] (M : o → Matrix m n α) :
    blockDiagonal (-M) = -blockDiagonal M :=
  map_neg (blockDiagonalAddMonoidHom m n o α) M
#align matrix.block_diagonal_neg Matrix.blockDiagonal_neg

/- warning: matrix.block_diagonal_sub -> Matrix.blockDiagonal_sub is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : AddGroup.{u4} α] (M : o -> (Matrix.{u1, u2, u4} m n α)) (N : o -> (Matrix.{u1, u2, u4} m n α)), Eq.{succ (max (max u1 u3) (max u2 u3) u4)} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) (HSub.hSub.{max u3 u1 u2 u4, max u3 u1 u2 u4, max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (o -> (Matrix.{u1, u2, u4} m n α)) (o -> (Matrix.{u1, u2, u4} m n α)) (instHSub.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (Pi.instSub.{u3, max u1 u2 u4} o (fun (ᾰ : o) => Matrix.{u1, u2, u4} m n α) (fun (i : o) => Matrix.hasSub.{u4, u1, u2} m n α (SubNegMonoid.toHasSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2))))) M N)) (HSub.hSub.{max (max u1 u3) (max u2 u3) u4, max (max u1 u3) (max u2 u3) u4, max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (instHSub.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.hasSub.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α (SubNegMonoid.toHasSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) M) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) N))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : AddGroup.{u4} α] (M : o -> (Matrix.{u3, u2, u4} m n α)) (N : o -> (Matrix.{u3, u2, u4} m n α)), Eq.{max (max (max (succ u3) (succ u2)) (succ u1)) (succ u4)} (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.blockDiagonal.{u3, u2, u1, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))) (HSub.hSub.{max (max (max u3 u2) u1) u4, max (max (max u3 u2) u1) u4, max (max (max u3 u2) u1) u4} (o -> (Matrix.{u3, u2, u4} m n α)) (o -> (Matrix.{u3, u2, u4} m n α)) (o -> (Matrix.{u3, u2, u4} m n α)) (instHSub.{max (max (max u3 u2) u1) u4} (o -> (Matrix.{u3, u2, u4} m n α)) (Pi.instSub.{u1, max (max u3 u2) u4} o (fun (ᾰ : o) => Matrix.{u3, u2, u4} m n α) (fun (i : o) => Matrix.sub.{u4, u3, u2} m n α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2))))) M N)) (HSub.hSub.{max (max (max u3 u2) u1) u4, max (max (max u3 u2) u1) u4, max (max (max u3 u2) u1) u4} (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (instHSub.{max (max (max u3 u2) u1) u4} (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.sub.{u4, max u3 u1, max u2 u1} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) (Matrix.blockDiagonal.{u3, u2, u1, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))) M) (Matrix.blockDiagonal.{u3, u2, u1, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))) N))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_sub Matrix.blockDiagonal_subₓ'. -/
@[simp]
theorem blockDiagonal_sub [AddGroup α] (M N : o → Matrix m n α) :
    blockDiagonal (M - N) = blockDiagonal M - blockDiagonal N :=
  map_sub (blockDiagonalAddMonoidHom m n o α) M N
#align matrix.block_diagonal_sub Matrix.blockDiagonal_sub

/- warning: matrix.block_diagonal_mul -> Matrix.blockDiagonal_mul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {p : Type.{u4}} {α : Type.{u5}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : Fintype.{u2} n] [_inst_3 : Fintype.{u3} o] [_inst_4 : NonUnitalNonAssocSemiring.{u5} α] (M : o -> (Matrix.{u1, u2, u5} m n α)) (N : o -> (Matrix.{u2, u4, u5} n p α)), Eq.{succ (max (max u1 u3) (max u4 u3) u5)} (Matrix.{max u1 u3, max u4 u3, u5} (Prod.{u1, u3} m o) (Prod.{u4, u3} p o) α) (Matrix.blockDiagonal.{u1, u4, u3, u5} m p o α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toHasZero.{u5} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u5} α _inst_4)) (fun (k : o) => Matrix.mul.{u5, u1, u2, u4} m n p α _inst_2 (Distrib.toHasMul.{u5} α (NonUnitalNonAssocSemiring.toDistrib.{u5} α _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α _inst_4) (M k) (N k))) (Matrix.mul.{u5, max u1 u3, max u2 u3, max u4 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) (Prod.{u4, u3} p o) α (Prod.fintype.{u2, u3} n o _inst_2 _inst_3) (Distrib.toHasMul.{u5} α (NonUnitalNonAssocSemiring.toDistrib.{u5} α _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α _inst_4) (Matrix.blockDiagonal.{u1, u2, u3, u5} m n o α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toHasZero.{u5} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u5} α _inst_4)) M) (Matrix.blockDiagonal.{u2, u4, u3, u5} n p o α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toHasZero.{u5} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u5} α _inst_4)) N))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u5}} {o : Type.{u4}} {p : Type.{u1}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u4} o] [_inst_2 : Fintype.{u5} n] [_inst_3 : Fintype.{u4} o] [_inst_4 : NonUnitalNonAssocSemiring.{u3} α] (M : o -> (Matrix.{u2, u5, u3} m n α)) (N : o -> (Matrix.{u5, u1, u3} n p α)), Eq.{max (max (max (succ u2) (succ u4)) (succ u1)) (succ u3)} (Matrix.{max u4 u2, max u4 u1, u3} (Prod.{u2, u4} m o) (Prod.{u1, u4} p o) α) (Matrix.blockDiagonal.{u2, u1, u4, u3} m p o α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_4)) (fun (k : o) => Matrix.mul.{u3, u2, u5, u1} m n p α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_4) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_4) (M k) (N k))) (Matrix.mul.{u3, max u4 u2, max u4 u5, max u4 u1} (Prod.{u2, u4} m o) (Prod.{u5, u4} n o) (Prod.{u1, u4} p o) α (instFintypeProd.{u5, u4} n o _inst_2 _inst_3) (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_4) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_4) (Matrix.blockDiagonal.{u2, u5, u4, u3} m n o α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_4)) M) (Matrix.blockDiagonal.{u5, u1, u4, u3} n p o α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_4)) N))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_mul Matrix.blockDiagonal_mulₓ'. -/
@[simp]
theorem blockDiagonal_mul [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
    (M : o → Matrix m n α) (N : o → Matrix n p α) :
    (blockDiagonal fun k => M k ⬝ N k) = blockDiagonal M ⬝ blockDiagonal N :=
  by
  ext (⟨i, k⟩⟨j, k'⟩)
  simp only [block_diagonal_apply, mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  split_ifs with h <;> simp [h]
#align matrix.block_diagonal_mul Matrix.blockDiagonal_mul

section

variable (α m o)

/- warning: matrix.block_diagonal_ring_hom -> Matrix.blockDiagonalRingHom is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u1}) (o : Type.{u2}) (α : Type.{u3}) [_inst_1 : DecidableEq.{succ u2} o] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : Fintype.{u2} o] [_inst_4 : Fintype.{u1} m] [_inst_5 : NonAssocSemiring.{u3} α], RingHom.{max u2 u1 u3, max (max u1 u2) u3} (o -> (Matrix.{u1, u1, u3} m m α)) (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) (Pi.nonAssocSemiring.{u2, max u1 u3} o (fun (ᾰ : o) => Matrix.{u1, u1, u3} m m α) (fun (i : o) => Matrix.nonAssocSemiring.{u3, u1} m α _inst_5 _inst_4 (fun (a : m) (b : m) => _inst_2 a b))) (Matrix.nonAssocSemiring.{u3, max u1 u2} (Prod.{u1, u2} m o) α _inst_5 (Prod.fintype.{u1, u2} m o _inst_4 _inst_3) (fun (a : Prod.{u1, u2} m o) (b : Prod.{u1, u2} m o) => Prod.decidableEq.{u1, u2} m o (fun (a : m) (b : m) => _inst_2 a b) (fun (a : o) (b : o) => _inst_1 a b) a b))
but is expected to have type
  forall (m : Type.{u1}) (o : Type.{u2}) (α : Type.{u3}) [_inst_1 : DecidableEq.{succ u2} o] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : Fintype.{u2} o] [_inst_4 : Fintype.{u1} m] [_inst_5 : NonAssocSemiring.{u3} α], RingHom.{max (max u1 u2) u3, max u3 u2 u1} (o -> (Matrix.{u1, u1, u3} m m α)) (Matrix.{max u2 u1, max u2 u1, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) (Pi.nonAssocSemiring.{u2, max u1 u3} o (fun (ᾰ : o) => Matrix.{u1, u1, u3} m m α) (fun (i : o) => Matrix.nonAssocSemiring.{u3, u1} m α _inst_5 _inst_4 (fun (a : m) (b : m) => _inst_2 a b))) (Matrix.nonAssocSemiring.{u3, max u1 u2} (Prod.{u1, u2} m o) α _inst_5 (instFintypeProd.{u1, u2} m o _inst_4 _inst_3) (fun (a : Prod.{u1, u2} m o) (b : Prod.{u1, u2} m o) => instDecidableEqProd.{u1, u2} m o (fun (a : m) (b : m) => _inst_2 a b) (fun (a : o) (b : o) => _inst_1 a b) a b))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_ring_hom Matrix.blockDiagonalRingHomₓ'. -/
/-- `matrix.block_diagonal` as a `ring_hom`. -/
@[simps]
def blockDiagonalRingHom [DecidableEq m] [Fintype o] [Fintype m] [NonAssocSemiring α] :
    (o → Matrix m m α) →+* Matrix (m × o) (m × o) α :=
  {
    blockDiagonalAddMonoidHom m m o α with
    toFun := blockDiagonal
    map_one' := blockDiagonal_one
    map_mul' := blockDiagonal_mul }
#align matrix.block_diagonal_ring_hom Matrix.blockDiagonalRingHom

end

/- warning: matrix.block_diagonal_pow -> Matrix.blockDiagonal_pow is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {o : Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} o] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : Fintype.{u2} o] [_inst_4 : Fintype.{u1} m] [_inst_5 : Semiring.{u3} α] (M : o -> (Matrix.{u1, u1, u3} m m α)) (n : Nat), Eq.{succ (max (max u1 u2) u3)} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) (Matrix.blockDiagonal.{u1, u1, u2, u3} m m o α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toHasZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_5)))) (HPow.hPow.{max u2 u1 u3, 0, max u2 u1 u3} (o -> (Matrix.{u1, u1, u3} m m α)) Nat (o -> (Matrix.{u1, u1, u3} m m α)) (instHPow.{max u2 u1 u3, 0} (o -> (Matrix.{u1, u1, u3} m m α)) Nat (Pi.hasPow.{u2, max u1 u3, 0} o Nat (fun (ᾰ : o) => Matrix.{u1, u1, u3} m m α) (fun (i : o) => Monoid.Pow.{max u1 u3} (Matrix.{u1, u1, u3} m m α) (MonoidWithZero.toMonoid.{max u1 u3} (Matrix.{u1, u1, u3} m m α) (Semiring.toMonoidWithZero.{max u1 u3} (Matrix.{u1, u1, u3} m m α) (Matrix.semiring.{u3, u1} m α _inst_5 _inst_4 (fun (a : m) (b : m) => _inst_2 a b))))))) M n)) (HPow.hPow.{max (max u1 u2) u3, 0, max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) Nat (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) (instHPow.{max (max u1 u2) u3, 0} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) Nat (Monoid.Pow.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) (MonoidWithZero.toMonoid.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) (Semiring.toMonoidWithZero.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) (Matrix.semiring.{u3, max u1 u2} (Prod.{u1, u2} m o) α _inst_5 (Prod.fintype.{u1, u2} m o _inst_4 _inst_3) (fun (a : Prod.{u1, u2} m o) (b : Prod.{u1, u2} m o) => Prod.decidableEq.{u1, u2} m o (fun (a : m) (b : m) => _inst_2 a b) (fun (a : o) (b : o) => _inst_1 a b) a b)))))) (Matrix.blockDiagonal.{u1, u1, u2, u3} m m o α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toHasZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_5)))) M) n)
but is expected to have type
  forall {m : Type.{u3}} {o : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} o] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : Fintype.{u2} o] [_inst_4 : Fintype.{u3} m] [_inst_5 : Semiring.{u1} α] (M : o -> (Matrix.{u3, u3, u1} m m α)) (n : Nat), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{max u2 u3, max u2 u3, u1} (Prod.{u3, u2} m o) (Prod.{u3, u2} m o) α) (Matrix.blockDiagonal.{u3, u3, u2, u1} m m o α (fun (a : o) (b : o) => _inst_1 a b) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_5)) (HPow.hPow.{max (max u3 u2) u1, 0, max (max u3 u2) u1} (o -> (Matrix.{u3, u3, u1} m m α)) Nat (o -> (Matrix.{u3, u3, u1} m m α)) (instHPow.{max (max u3 u2) u1, 0} (o -> (Matrix.{u3, u3, u1} m m α)) Nat (Pi.instPow.{u2, max u3 u1, 0} o Nat (fun (ᾰ : o) => Matrix.{u3, u3, u1} m m α) (fun (i : o) => Monoid.Pow.{max u3 u1} (Matrix.{u3, u3, u1} m m α) (MonoidWithZero.toMonoid.{max u3 u1} (Matrix.{u3, u3, u1} m m α) (Semiring.toMonoidWithZero.{max u3 u1} (Matrix.{u3, u3, u1} m m α) (Matrix.semiring.{u1, u3} m α _inst_5 _inst_4 (fun (a : m) (b : m) => _inst_2 a b))))))) M n)) (HPow.hPow.{max (max u3 u2) u1, 0, max (max u3 u2) u1} (Matrix.{max u2 u3, max u2 u3, u1} (Prod.{u3, u2} m o) (Prod.{u3, u2} m o) α) Nat (Matrix.{max u2 u3, max u2 u3, u1} (Prod.{u3, u2} m o) (Prod.{u3, u2} m o) α) (instHPow.{max (max u3 u2) u1, 0} (Matrix.{max u2 u3, max u2 u3, u1} (Prod.{u3, u2} m o) (Prod.{u3, u2} m o) α) Nat (Monoid.Pow.{max (max u3 u2) u1} (Matrix.{max u2 u3, max u2 u3, u1} (Prod.{u3, u2} m o) (Prod.{u3, u2} m o) α) (MonoidWithZero.toMonoid.{max (max u3 u2) u1} (Matrix.{max u2 u3, max u2 u3, u1} (Prod.{u3, u2} m o) (Prod.{u3, u2} m o) α) (Semiring.toMonoidWithZero.{max (max u3 u2) u1} (Matrix.{max u2 u3, max u2 u3, u1} (Prod.{u3, u2} m o) (Prod.{u3, u2} m o) α) (Matrix.semiring.{u1, max u3 u2} (Prod.{u3, u2} m o) α _inst_5 (instFintypeProd.{u3, u2} m o _inst_4 _inst_3) (fun (a : Prod.{u3, u2} m o) (b : Prod.{u3, u2} m o) => instDecidableEqProd.{u3, u2} m o (fun (a : m) (b : m) => _inst_2 a b) (fun (a : o) (b : o) => _inst_1 a b) a b)))))) (Matrix.blockDiagonal.{u3, u3, u2, u1} m m o α (fun (a : o) (b : o) => _inst_1 a b) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_5)) M) n)
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_pow Matrix.blockDiagonal_powₓ'. -/
@[simp]
theorem blockDiagonal_pow [DecidableEq m] [Fintype o] [Fintype m] [Semiring α]
    (M : o → Matrix m m α) (n : ℕ) : blockDiagonal (M ^ n) = blockDiagonal M ^ n :=
  map_pow (blockDiagonalRingHom m o α) M n
#align matrix.block_diagonal_pow Matrix.blockDiagonal_pow

/- warning: matrix.block_diagonal_smul -> Matrix.blockDiagonal_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] {R : Type.{u5}} [_inst_2 : Monoid.{u5} R] [_inst_3 : AddMonoid.{u4} α] [_inst_4 : DistribMulAction.{u5, u4} R α _inst_2 _inst_3] (x : R) (M : o -> (Matrix.{u1, u2, u4} m n α)), Eq.{succ (max (max u1 u3) (max u2 u3) u4)} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_3)) (SMul.smul.{u5, max u3 u1 u2 u4} R (o -> (Matrix.{u1, u2, u4} m n α)) (Function.hasSMul.{u3, u5, max u1 u2 u4} o R (Matrix.{u1, u2, u4} m n α) (Matrix.hasSmul.{u4, u1, u2, u5} m n R α (SMulZeroClass.toHasSmul.{u5, u4} R α (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_3)) (DistribSMul.toSmulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_3) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_2 _inst_3 _inst_4))))) x M)) (SMul.smul.{u5, max (max u1 u3) (max u2 u3) u4} R (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.hasSmul.{u4, max u1 u3, max u2 u3, u5} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) R α (SMulZeroClass.toHasSmul.{u5, u4} R α (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_3)) (DistribSMul.toSmulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_3) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_2 _inst_3 _inst_4)))) x (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_3)) M))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] {R : Type.{u5}} [_inst_2 : Monoid.{u5} R] [_inst_3 : AddMonoid.{u4} α] [_inst_4 : DistribMulAction.{u5, u4} R α _inst_2 _inst_3] (x : R) (M : o -> (Matrix.{u3, u2, u4} m n α)), Eq.{max (max (max (succ u3) (succ u2)) (succ u1)) (succ u4)} (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.blockDiagonal.{u3, u2, u1, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddMonoid.toZero.{u4} α _inst_3) (HSMul.hSMul.{u5, max (max (max u3 u2) u1) u4, max (max (max u3 u2) u1) u4} R (o -> (Matrix.{u3, u2, u4} m n α)) (o -> (Matrix.{u3, u2, u4} m n α)) (instHSMul.{u5, max (max (max u3 u2) u1) u4} R (o -> (Matrix.{u3, u2, u4} m n α)) (Pi.instSMul.{u1, max (max u3 u2) u4, u5} o R (fun (a._@.Mathlib.Data.Matrix.Block._hyg.5722 : o) => Matrix.{u3, u2, u4} m n α) (fun (i : o) => Matrix.smul.{u4, u3, u2, u5} m n R α (SMulZeroClass.toSMul.{u5, u4} R α (AddMonoid.toZero.{u4} α _inst_3) (DistribSMul.toSMulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_3) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_2 _inst_3 _inst_4)))))) x M)) (HSMul.hSMul.{u5, max (max (max u4 u1) u2) u3, max (max (max u3 u2) u1) u4} R (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (instHSMul.{u5, max (max (max u3 u2) u1) u4} R (Matrix.{max u1 u3, max u1 u2, u4} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) α) (Matrix.smul.{u4, max u3 u1, max u2 u1, u5} (Prod.{u3, u1} m o) (Prod.{u2, u1} n o) R α (SMulZeroClass.toSMul.{u5, u4} R α (AddMonoid.toZero.{u4} α _inst_3) (DistribSMul.toSMulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_3) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_2 _inst_3 _inst_4))))) x (Matrix.blockDiagonal.{u3, u2, u1, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) (AddMonoid.toZero.{u4} α _inst_3) M))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_smul Matrix.blockDiagonal_smulₓ'. -/
@[simp]
theorem blockDiagonal_smul {R : Type _} [Monoid R] [AddMonoid α] [DistribMulAction R α] (x : R)
    (M : o → Matrix m n α) : blockDiagonal (x • M) = x • blockDiagonal M := by ext;
  simp only [block_diagonal_apply, Pi.smul_apply]; split_ifs <;> simp
#align matrix.block_diagonal_smul Matrix.blockDiagonal_smul

end BlockDiagonal

section BlockDiag

#print Matrix.blockDiag /-
/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `matrix.diag`, and the left-inverse of `matrix.block_diagonal`. -/
def blockDiag (M : Matrix (m × o) (n × o) α) (k : o) : Matrix m n α :=
  of fun i j => M (i, k) (j, k)
#align matrix.block_diag Matrix.blockDiag
-/

/- warning: matrix.block_diag_apply -> Matrix.blockDiag_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} (M : Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (k : o) (i : m) (j : n), Eq.{succ u4} α (Matrix.blockDiag.{u1, u2, u3, u4} m n o α M k i j) (M (Prod.mk.{u1, u3} m o i k) (Prod.mk.{u2, u3} n o j k))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u4}} {α : Type.{u1}} (M : Matrix.{max u4 u3, max u4 u2, u1} (Prod.{u3, u4} m o) (Prod.{u2, u4} n o) α) (k : o) (i : m) (j : n), Eq.{succ u1} α (Matrix.blockDiag.{u3, u2, u4, u1} m n o α M k i j) (M (Prod.mk.{u3, u4} m o i k) (Prod.mk.{u2, u4} n o j k))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_apply Matrix.blockDiag_applyₓ'. -/
-- TODO: set as an equation lemma for `block_diag`, see mathlib4#3024
theorem blockDiag_apply (M : Matrix (m × o) (n × o) α) (k : o) (i j) :
    blockDiag M k i j = M (i, k) (j, k) :=
  rfl
#align matrix.block_diag_apply Matrix.blockDiag_apply

/- warning: matrix.block_diag_map -> Matrix.blockDiag_map is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} {β : Type.{u5}} (M : Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (f : α -> β), Eq.{max (succ u3) (succ (max u1 u2 u5))} (o -> (Matrix.{u1, u2, u5} m n β)) (Matrix.blockDiag.{u1, u2, u3, u5} m n o β (Matrix.map.{u4, u5, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α β M f)) (fun (k : o) => Matrix.map.{u4, u5, u1, u2} m n α β (Matrix.blockDiag.{u1, u2, u3, u4} m n o α M k) f)
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u5}} {α : Type.{u2}} {β : Type.{u1}} (M : Matrix.{max u5 u4, max u5 u3, u2} (Prod.{u4, u5} m o) (Prod.{u3, u5} n o) α) (f : α -> β), Eq.{max (max (max (succ u4) (succ u3)) (succ u5)) (succ u1)} (o -> (Matrix.{u4, u3, u1} m n β)) (Matrix.blockDiag.{u4, u3, u5, u1} m n o β (Matrix.map.{u2, u1, max u4 u5, max u3 u5} (Prod.{u4, u5} m o) (Prod.{u3, u5} n o) α β M f)) (fun (k : o) => Matrix.map.{u2, u1, u4, u3} m n α β (Matrix.blockDiag.{u4, u3, u5, u2} m n o α M k) f)
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_map Matrix.blockDiag_mapₓ'. -/
theorem blockDiag_map (M : Matrix (m × o) (n × o) α) (f : α → β) :
    blockDiag (M.map f) = fun k => (blockDiag M k).map f :=
  rfl
#align matrix.block_diag_map Matrix.blockDiag_map

/- warning: matrix.block_diag_transpose -> Matrix.blockDiag_transpose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} (M : Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (k : o), Eq.{succ (max u2 u1 u4)} (Matrix.{u2, u1, u4} n m α) (Matrix.blockDiag.{u2, u1, u3, u4} n m o α (Matrix.transpose.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α M) k) (Matrix.transpose.{u4, u1, u2} m n α (Matrix.blockDiag.{u1, u2, u3, u4} m n o α M k))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u4}} {α : Type.{u1}} (M : Matrix.{max u4 u3, max u4 u2, u1} (Prod.{u3, u4} m o) (Prod.{u2, u4} n o) α) (k : o), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u3, u1} n m α) (Matrix.blockDiag.{u2, u3, u4, u1} n m o α (Matrix.transpose.{u1, max u4 u3, max u4 u2} (Prod.{u3, u4} m o) (Prod.{u2, u4} n o) α M) k) (Matrix.transpose.{u1, u3, u2} m n α (Matrix.blockDiag.{u3, u2, u4, u1} m n o α M k))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_transpose Matrix.blockDiag_transposeₓ'. -/
@[simp]
theorem blockDiag_transpose (M : Matrix (m × o) (n × o) α) (k : o) :
    blockDiag Mᵀ k = (blockDiag M k)ᵀ :=
  ext fun i j => rfl
#align matrix.block_diag_transpose Matrix.blockDiag_transpose

/- warning: matrix.block_diag_conj_transpose -> Matrix.blockDiag_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : AddMonoid.{u4} α] [_inst_2 : StarAddMonoid.{u4} α _inst_1] (M : Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (k : o), Eq.{succ (max u2 u1 u4)} (Matrix.{u2, u1, u4} n m α) (Matrix.blockDiag.{u2, u1, u3, u4} n m o α (Matrix.conjTranspose.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α (InvolutiveStar.toHasStar.{u4} α (StarAddMonoid.toHasInvolutiveStar.{u4} α _inst_1 _inst_2)) M) k) (Matrix.conjTranspose.{u4, u1, u2} m n α (InvolutiveStar.toHasStar.{u4} α (StarAddMonoid.toHasInvolutiveStar.{u4} α _inst_1 _inst_2)) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α M k))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : AddMonoid.{u4} α] [_inst_2 : StarAddMonoid.{u4} α _inst_1] (M : Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (k : o), Eq.{max (max (succ u2) (succ u1)) (succ u4)} (Matrix.{u1, u2, u4} n m α) (Matrix.blockDiag.{u1, u2, u3, u4} n m o α (Matrix.conjTranspose.{u4, max u3 u2, max u3 u1} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α _inst_1 _inst_2)) M) k) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α _inst_1 _inst_2)) (Matrix.blockDiag.{u2, u1, u3, u4} m n o α M k))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_conj_transpose Matrix.blockDiag_conjTransposeₓ'. -/
@[simp]
theorem blockDiag_conjTranspose {α : Type _} [AddMonoid α] [StarAddMonoid α]
    (M : Matrix (m × o) (n × o) α) (k : o) : blockDiag Mᴴ k = (blockDiag M k)ᴴ :=
  ext fun i j => rfl
#align matrix.block_diag_conj_transpose Matrix.blockDiag_conjTranspose

section Zero

variable [Zero α] [Zero β]

/- warning: matrix.block_diag_zero -> Matrix.blockDiag_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : Zero.{u4} α], Eq.{max (succ u3) (succ (max u1 u2 u4))} (o -> (Matrix.{u1, u2, u4} m n α)) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α (OfNat.ofNat.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) 0 (OfNat.mk.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) 0 (Zero.zero.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.hasZero.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α _inst_1))))) (OfNat.ofNat.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) 0 (OfNat.mk.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) 0 (Zero.zero.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (Pi.instZero.{u3, max u1 u2 u4} o (fun (k : o) => Matrix.{u1, u2, u4} m n α) (fun (i : o) => Matrix.hasZero.{u4, u1, u2} m n α _inst_1)))))
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α], Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (o -> (Matrix.{u4, u3, u1} m n α)) (Matrix.blockDiag.{u4, u3, u2, u1} m n o α (OfNat.ofNat.{max (max (max u4 u3) u2) u1} (Matrix.{max u2 u4, max u2 u3, u1} (Prod.{u4, u2} m o) (Prod.{u3, u2} n o) α) 0 (Zero.toOfNat0.{max (max (max u4 u3) u2) u1} (Matrix.{max u2 u4, max u2 u3, u1} (Prod.{u4, u2} m o) (Prod.{u3, u2} n o) α) (Matrix.zero.{u1, max u4 u2, max u3 u2} (Prod.{u4, u2} m o) (Prod.{u3, u2} n o) α _inst_1)))) (OfNat.ofNat.{max (max (max u4 u3) u2) u1} (o -> (Matrix.{u4, u3, u1} m n α)) 0 (Zero.toOfNat0.{max (max (max u4 u3) u2) u1} (o -> (Matrix.{u4, u3, u1} m n α)) (Pi.instZero.{u2, max (max u4 u3) u1} o (fun (k : o) => Matrix.{u4, u3, u1} m n α) (fun (i : o) => Matrix.zero.{u1, u4, u3} m n α _inst_1))))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_zero Matrix.blockDiag_zeroₓ'. -/
@[simp]
theorem blockDiag_zero : blockDiag (0 : Matrix (m × o) (n × o) α) = 0 :=
  rfl
#align matrix.block_diag_zero Matrix.blockDiag_zero

/- warning: matrix.block_diag_diagonal -> Matrix.blockDiag_diagonal is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {o : Type.{u2}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α] [_inst_3 : DecidableEq.{succ u2} o] [_inst_4 : DecidableEq.{succ u1} m] (d : (Prod.{u1, u2} m o) -> α) (k : o), Eq.{succ (max u1 u3)} (Matrix.{u1, u1, u3} m m α) (Matrix.blockDiag.{u1, u1, u2, u3} m m o α (Matrix.diagonal.{u3, max u1 u2} (Prod.{u1, u2} m o) α (fun (a : Prod.{u1, u2} m o) (b : Prod.{u1, u2} m o) => Prod.decidableEq.{u1, u2} m o (fun (a : m) (b : m) => _inst_4 a b) (fun (a : o) (b : o) => _inst_3 a b) a b) _inst_1 d) k) (Matrix.diagonal.{u3, u1} m α (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (fun (i : m) => d (Prod.mk.{u1, u2} m o i k)))
but is expected to have type
  forall {m : Type.{u2}} {o : Type.{u3}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_3 : DecidableEq.{succ u3} o] [_inst_4 : DecidableEq.{succ u2} m] (d : (Prod.{u2, u3} m o) -> α) (k : o), Eq.{max (succ u2) (succ u1)} (Matrix.{u2, u2, u1} m m α) (Matrix.blockDiag.{u2, u2, u3, u1} m m o α (Matrix.diagonal.{u1, max u3 u2} (Prod.{u2, u3} m o) α (fun (a : Prod.{u2, u3} m o) (b : Prod.{u2, u3} m o) => instDecidableEqProd.{u2, u3} m o (fun (a : m) (b : m) => _inst_4 a b) (fun (a : o) (b : o) => _inst_3 a b) a b) _inst_1 d) k) (Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (fun (i : m) => d (Prod.mk.{u2, u3} m o i k)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_diagonal Matrix.blockDiag_diagonalₓ'. -/
@[simp]
theorem blockDiag_diagonal [DecidableEq o] [DecidableEq m] (d : m × o → α) (k : o) :
    blockDiag (diagonal d) k = diagonal fun i => d (i, k) :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [block_diag_apply, diagonal_apply_eq, diagonal_apply_eq]
    · rw [block_diag_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt _ hij)]
      exact prod.fst_eq_iff.mpr
#align matrix.block_diag_diagonal Matrix.blockDiag_diagonal

/- warning: matrix.block_diag_block_diagonal -> Matrix.blockDiag_blockDiagonal is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : Zero.{u4} α] [_inst_3 : DecidableEq.{succ u3} o] (M : o -> (Matrix.{u1, u2, u4} m n α)), Eq.{max (succ u3) (succ (max u1 u2 u4))} (o -> (Matrix.{u1, u2, u4} m n α)) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 M)) M
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_3 : DecidableEq.{succ u4} o] (M : o -> (Matrix.{u3, u2, u1} m n α)), Eq.{max (max (max (succ u3) (succ u2)) (succ u4)) (succ u1)} (o -> (Matrix.{u3, u2, u1} m n α)) (Matrix.blockDiag.{u3, u2, u4, u1} m n o α (Matrix.blockDiagonal.{u3, u2, u4, u1} m n o α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 M)) M
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_block_diagonal Matrix.blockDiag_blockDiagonalₓ'. -/
@[simp]
theorem blockDiag_blockDiagonal [DecidableEq o] (M : o → Matrix m n α) :
    blockDiag (blockDiagonal M) = M :=
  funext fun k => ext fun i j => blockDiagonal_apply_eq M i j _
#align matrix.block_diag_block_diagonal Matrix.blockDiag_blockDiagonal

/- warning: matrix.block_diagonal_injective -> Matrix.blockDiagonal_injective is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : Zero.{u4} α] [_inst_3 : DecidableEq.{succ u3} o], Function.Injective.{max (succ u3) (succ (max u1 u2 u4)), succ (max (max u1 u3) (max u2 u3) u4)} (o -> (Matrix.{u1, u2, u4} m n α)) (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_3 a b) _inst_1)
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_3 : DecidableEq.{succ u4} o], Function.Injective.{max (max (max (succ u3) (succ u2)) (succ u4)) (succ u1), max (max (max (succ u3) (succ u2)) (succ u4)) (succ u1)} (o -> (Matrix.{u3, u2, u1} m n α)) (Matrix.{max u4 u3, max u4 u2, u1} (Prod.{u3, u4} m o) (Prod.{u2, u4} n o) α) (Matrix.blockDiagonal.{u3, u2, u4, u1} m n o α (fun (a : o) (b : o) => _inst_3 a b) _inst_1)
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_injective Matrix.blockDiagonal_injectiveₓ'. -/
theorem blockDiagonal_injective [DecidableEq o] :
    Function.Injective (blockDiagonal : (o → Matrix m n α) → Matrix _ _ α) :=
  Function.LeftInverse.injective blockDiag_blockDiagonal
#align matrix.block_diagonal_injective Matrix.blockDiagonal_injective

/- warning: matrix.block_diagonal_inj -> Matrix.blockDiagonal_inj is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : Zero.{u4} α] [_inst_3 : DecidableEq.{succ u3} o] {M : o -> (Matrix.{u1, u2, u4} m n α)} {N : o -> (Matrix.{u1, u2, u4} m n α)}, Iff (Eq.{succ (max (max u1 u3) (max u2 u3) u4)} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 M) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 N)) (Eq.{max (succ u3) (succ (max u1 u2 u4))} (o -> (Matrix.{u1, u2, u4} m n α)) M N)
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_3 : DecidableEq.{succ u4} o] {M : o -> (Matrix.{u3, u2, u1} m n α)} {N : o -> (Matrix.{u3, u2, u1} m n α)}, Iff (Eq.{max (max (max (succ u3) (succ u2)) (succ u4)) (succ u1)} (Matrix.{max u4 u3, max u4 u2, u1} (Prod.{u3, u4} m o) (Prod.{u2, u4} n o) α) (Matrix.blockDiagonal.{u3, u2, u4, u1} m n o α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 M) (Matrix.blockDiagonal.{u3, u2, u4, u1} m n o α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 N)) (Eq.{max (max (max (succ u3) (succ u2)) (succ u4)) (succ u1)} (o -> (Matrix.{u3, u2, u1} m n α)) M N)
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_inj Matrix.blockDiagonal_injₓ'. -/
@[simp]
theorem blockDiagonal_inj [DecidableEq o] {M N : o → Matrix m n α} :
    blockDiagonal M = blockDiagonal N ↔ M = N :=
  blockDiagonal_injective.eq_iff
#align matrix.block_diagonal_inj Matrix.blockDiagonal_inj

/- warning: matrix.block_diag_one -> Matrix.blockDiag_one is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {o : Type.{u2}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α] [_inst_3 : DecidableEq.{succ u2} o] [_inst_4 : DecidableEq.{succ u1} m] [_inst_5 : One.{u3} α], Eq.{max (succ u2) (succ (max u1 u3))} (o -> (Matrix.{u1, u1, u3} m m α)) (Matrix.blockDiag.{u1, u1, u2, u3} m m o α (OfNat.ofNat.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) 1 (OfNat.mk.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) 1 (One.one.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Prod.{u1, u2} m o) (Prod.{u1, u2} m o) α) (Matrix.hasOne.{u3, max u1 u2} (Prod.{u1, u2} m o) α (fun (a : Prod.{u1, u2} m o) (b : Prod.{u1, u2} m o) => Prod.decidableEq.{u1, u2} m o (fun (a : m) (b : m) => _inst_4 a b) (fun (a : o) (b : o) => _inst_3 a b) a b) _inst_1 _inst_5))))) (OfNat.ofNat.{max u2 u1 u3} (o -> (Matrix.{u1, u1, u3} m m α)) 1 (OfNat.mk.{max u2 u1 u3} (o -> (Matrix.{u1, u1, u3} m m α)) 1 (One.one.{max u2 u1 u3} (o -> (Matrix.{u1, u1, u3} m m α)) (Pi.instOne.{u2, max u1 u3} o (fun (k : o) => Matrix.{u1, u1, u3} m m α) (fun (i : o) => Matrix.hasOne.{u3, u1} m α (fun (a : m) (b : m) => _inst_4 a b) _inst_1 _inst_5)))))
but is expected to have type
  forall {m : Type.{u2}} {o : Type.{u3}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_3 : DecidableEq.{succ u3} o] [_inst_4 : DecidableEq.{succ u2} m] [_inst_5 : One.{u1} α], Eq.{max (max (succ u2) (succ u3)) (succ u1)} (o -> (Matrix.{u2, u2, u1} m m α)) (Matrix.blockDiag.{u2, u2, u3, u1} m m o α (OfNat.ofNat.{max (max u2 u3) u1} (Matrix.{max u3 u2, max u3 u2, u1} (Prod.{u2, u3} m o) (Prod.{u2, u3} m o) α) 1 (One.toOfNat1.{max (max u2 u3) u1} (Matrix.{max u3 u2, max u3 u2, u1} (Prod.{u2, u3} m o) (Prod.{u2, u3} m o) α) (Matrix.one.{u1, max u2 u3} (Prod.{u2, u3} m o) α (fun (a : Prod.{u2, u3} m o) (b : Prod.{u2, u3} m o) => instDecidableEqProd.{u2, u3} m o (fun (a : m) (b : m) => _inst_4 a b) (fun (a : o) (b : o) => _inst_3 a b) a b) _inst_1 _inst_5)))) (OfNat.ofNat.{max (max u2 u3) u1} (o -> (Matrix.{u2, u2, u1} m m α)) 1 (One.toOfNat1.{max (max u2 u3) u1} (o -> (Matrix.{u2, u2, u1} m m α)) (Pi.instOne.{u3, max u2 u1} o (fun (k : o) => Matrix.{u2, u2, u1} m m α) (fun (i : o) => Matrix.one.{u1, u2} m α (fun (a : m) (b : m) => _inst_4 a b) _inst_1 _inst_5))))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_one Matrix.blockDiag_oneₓ'. -/
@[simp]
theorem blockDiag_one [DecidableEq o] [DecidableEq m] [One α] :
    blockDiag (1 : Matrix (m × o) (m × o) α) = 1 :=
  funext <| blockDiag_diagonal _
#align matrix.block_diag_one Matrix.blockDiag_one

end Zero

/- warning: matrix.block_diag_add -> Matrix.blockDiag_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : AddZeroClass.{u4} α] (M : Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (N : Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α), Eq.{max (succ u3) (succ (max u1 u2 u4))} (o -> (Matrix.{u1, u2, u4} m n α)) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α (HAdd.hAdd.{max (max u1 u3) (max u2 u3) u4, max (max u1 u3) (max u2 u3) u4, max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (instHAdd.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.hasAdd.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α (AddZeroClass.toHasAdd.{u4} α _inst_1))) M N)) (HAdd.hAdd.{max u3 u1 u2 u4, max u3 u1 u2 u4, max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (o -> (Matrix.{u1, u2, u4} m n α)) (o -> (Matrix.{u1, u2, u4} m n α)) (instHAdd.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (Pi.instAdd.{u3, max u1 u2 u4} o (fun (k : o) => Matrix.{u1, u2, u4} m n α) (fun (i : o) => Matrix.hasAdd.{u4, u1, u2} m n α (AddZeroClass.toHasAdd.{u4} α _inst_1)))) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α M) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α N))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : AddZeroClass.{u4} α] (M : Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (N : Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α), Eq.{max (max (max (succ u2) (succ u1)) (succ u3)) (succ u4)} (o -> (Matrix.{u2, u1, u4} m n α)) (Matrix.blockDiag.{u2, u1, u3, u4} m n o α (HAdd.hAdd.{max (max (max u2 u1) u3) u4, max (max (max u2 u1) u3) u4, max (max (max u2 u1) u3) u4} (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (instHAdd.{max (max (max u2 u1) u3) u4} (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (Matrix.add.{u4, max u2 u3, max u1 u3} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α (AddZeroClass.toAdd.{u4} α _inst_1))) M N)) (HAdd.hAdd.{max (max (max u2 u1) u3) u4, max (max (max u2 u1) u3) u4, max (max (max u2 u1) u3) u4} (o -> (Matrix.{u2, u1, u4} m n α)) (o -> (Matrix.{u2, u1, u4} m n α)) (o -> (Matrix.{u2, u1, u4} m n α)) (instHAdd.{max (max (max u2 u1) u3) u4} (o -> (Matrix.{u2, u1, u4} m n α)) (Pi.instAdd.{u3, max (max u2 u1) u4} o (fun (k : o) => Matrix.{u2, u1, u4} m n α) (fun (i : o) => Matrix.add.{u4, u2, u1} m n α (AddZeroClass.toAdd.{u4} α _inst_1)))) (Matrix.blockDiag.{u2, u1, u3, u4} m n o α M) (Matrix.blockDiag.{u2, u1, u3, u4} m n o α N))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_add Matrix.blockDiag_addₓ'. -/
@[simp]
theorem blockDiag_add [AddZeroClass α] (M N : Matrix (m × o) (n × o) α) :
    blockDiag (M + N) = blockDiag M + blockDiag N :=
  rfl
#align matrix.block_diag_add Matrix.blockDiag_add

section

variable (o m n α)

#print Matrix.blockDiagAddMonoidHom /-
/-- `matrix.block_diag` as an `add_monoid_hom`. -/
@[simps]
def blockDiagAddMonoidHom [AddZeroClass α] : Matrix (m × o) (n × o) α →+ o → Matrix m n α
    where
  toFun := blockDiag
  map_zero' := blockDiag_zero
  map_add' := blockDiag_add
#align matrix.block_diag_add_monoid_hom Matrix.blockDiagAddMonoidHom
-/

end

/- warning: matrix.block_diag_neg -> Matrix.blockDiag_neg is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : AddGroup.{u4} α] (M : Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α), Eq.{max (succ u3) (succ (max u1 u2 u4))} (o -> (Matrix.{u1, u2, u4} m n α)) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α (Neg.neg.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.hasNeg.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α (SubNegMonoid.toHasNeg.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1))) M)) (Neg.neg.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (Pi.instNeg.{u3, max u1 u2 u4} o (fun (k : o) => Matrix.{u1, u2, u4} m n α) (fun (i : o) => Matrix.hasNeg.{u4, u1, u2} m n α (SubNegMonoid.toHasNeg.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1)))) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : AddGroup.{u4} α] (M : Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α), Eq.{max (max (max (succ u2) (succ u1)) (succ u3)) (succ u4)} (o -> (Matrix.{u2, u1, u4} m n α)) (Matrix.blockDiag.{u2, u1, u3, u4} m n o α (Neg.neg.{max (max (max u2 u1) u3) u4} (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (Matrix.neg.{u4, max u2 u3, max u1 u3} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_1))))) M)) (Neg.neg.{max (max (max u2 u1) u3) u4} (o -> (Matrix.{u2, u1, u4} m n α)) (Pi.instNeg.{u3, max (max u2 u1) u4} o (fun (k : o) => Matrix.{u2, u1, u4} m n α) (fun (i : o) => Matrix.neg.{u4, u2, u1} m n α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_1)))))) (Matrix.blockDiag.{u2, u1, u3, u4} m n o α M))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_neg Matrix.blockDiag_negₓ'. -/
@[simp]
theorem blockDiag_neg [AddGroup α] (M : Matrix (m × o) (n × o) α) : blockDiag (-M) = -blockDiag M :=
  map_neg (blockDiagAddMonoidHom m n o α) M
#align matrix.block_diag_neg Matrix.blockDiag_neg

/- warning: matrix.block_diag_sub -> Matrix.blockDiag_sub is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : AddGroup.{u4} α] (M : Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (N : Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α), Eq.{max (succ u3) (succ (max u1 u2 u4))} (o -> (Matrix.{u1, u2, u4} m n α)) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α (HSub.hSub.{max (max u1 u3) (max u2 u3) u4, max (max u1 u3) (max u2 u3) u4, max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (instHSub.{max (max u1 u3) (max u2 u3) u4} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.hasSub.{u4, max u1 u3, max u2 u3} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α (SubNegMonoid.toHasSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1)))) M N)) (HSub.hSub.{max u3 u1 u2 u4, max u3 u1 u2 u4, max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (o -> (Matrix.{u1, u2, u4} m n α)) (o -> (Matrix.{u1, u2, u4} m n α)) (instHSub.{max u3 u1 u2 u4} (o -> (Matrix.{u1, u2, u4} m n α)) (Pi.instSub.{u3, max u1 u2 u4} o (fun (k : o) => Matrix.{u1, u2, u4} m n α) (fun (i : o) => Matrix.hasSub.{u4, u1, u2} m n α (SubNegMonoid.toHasSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1))))) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α M) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α N))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : AddGroup.{u4} α] (M : Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (N : Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α), Eq.{max (max (max (succ u2) (succ u1)) (succ u3)) (succ u4)} (o -> (Matrix.{u2, u1, u4} m n α)) (Matrix.blockDiag.{u2, u1, u3, u4} m n o α (HSub.hSub.{max (max (max u2 u1) u3) u4, max (max (max u2 u1) u3) u4, max (max (max u2 u1) u3) u4} (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (instHSub.{max (max (max u2 u1) u3) u4} (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (Matrix.sub.{u4, max u2 u3, max u1 u3} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1)))) M N)) (HSub.hSub.{max (max (max u2 u1) u3) u4, max (max (max u2 u1) u3) u4, max (max (max u2 u1) u3) u4} (o -> (Matrix.{u2, u1, u4} m n α)) (o -> (Matrix.{u2, u1, u4} m n α)) (o -> (Matrix.{u2, u1, u4} m n α)) (instHSub.{max (max (max u2 u1) u3) u4} (o -> (Matrix.{u2, u1, u4} m n α)) (Pi.instSub.{u3, max (max u2 u1) u4} o (fun (k : o) => Matrix.{u2, u1, u4} m n α) (fun (i : o) => Matrix.sub.{u4, u2, u1} m n α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1))))) (Matrix.blockDiag.{u2, u1, u3, u4} m n o α M) (Matrix.blockDiag.{u2, u1, u3, u4} m n o α N))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_sub Matrix.blockDiag_subₓ'. -/
@[simp]
theorem blockDiag_sub [AddGroup α] (M N : Matrix (m × o) (n × o) α) :
    blockDiag (M - N) = blockDiag M - blockDiag N :=
  map_sub (blockDiagAddMonoidHom m n o α) M N
#align matrix.block_diag_sub Matrix.blockDiag_sub

/- warning: matrix.block_diag_smul -> Matrix.blockDiag_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} {R : Type.{u5}} [_inst_1 : Monoid.{u5} R] [_inst_2 : AddMonoid.{u4} α] [_inst_3 : DistribMulAction.{u5, u4} R α _inst_1 _inst_2] (x : R) (M : Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α), Eq.{max (succ u3) (succ (max u1 u2 u4))} (o -> (Matrix.{u1, u2, u4} m n α)) (Matrix.blockDiag.{u1, u2, u3, u4} m n o α (SMul.smul.{u5, max (max u1 u3) (max u2 u3) u4} R (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.hasSmul.{u4, max u1 u3, max u2 u3, u5} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) R α (SMulZeroClass.toHasSmul.{u5, u4} R α (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_2)) (DistribSMul.toSmulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_2) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_1 _inst_2 _inst_3)))) x M)) (SMul.smul.{u5, max u3 u1 u2 u4} R (o -> (Matrix.{u1, u2, u4} m n α)) (Function.hasSMul.{u3, u5, max u1 u2 u4} o R (Matrix.{u1, u2, u4} m n α) (Matrix.hasSmul.{u4, u1, u2, u5} m n R α (SMulZeroClass.toHasSmul.{u5, u4} R α (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_2)) (DistribSMul.toSmulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_2) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_1 _inst_2 _inst_3))))) x (Matrix.blockDiag.{u1, u2, u3, u4} m n o α M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {o : Type.{u3}} {α : Type.{u4}} {R : Type.{u5}} [_inst_1 : Monoid.{u5} R] [_inst_2 : AddMonoid.{u4} α] [_inst_3 : DistribMulAction.{u5, u4} R α _inst_1 _inst_2] (x : R) (M : Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α), Eq.{max (max (max (succ u2) (succ u1)) (succ u3)) (succ u4)} (o -> (Matrix.{u2, u1, u4} m n α)) (Matrix.blockDiag.{u2, u1, u3, u4} m n o α (HSMul.hSMul.{u5, max (max (max u2 u1) u3) u4, max (max (max u2 u1) u3) u4} R (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (instHSMul.{u5, max (max (max u2 u1) u3) u4} R (Matrix.{max u3 u2, max u3 u1, u4} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) α) (Matrix.smul.{u4, max u2 u3, max u1 u3, u5} (Prod.{u2, u3} m o) (Prod.{u1, u3} n o) R α (SMulZeroClass.toSMul.{u5, u4} R α (AddMonoid.toZero.{u4} α _inst_2) (DistribSMul.toSMulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_2) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_1 _inst_2 _inst_3))))) x M)) (HSMul.hSMul.{u5, max (max (max u4 u3) u1) u2, max (max (max u2 u1) u3) u4} R (o -> (Matrix.{u2, u1, u4} m n α)) (o -> (Matrix.{u2, u1, u4} m n α)) (instHSMul.{u5, max (max (max u2 u1) u3) u4} R (o -> (Matrix.{u2, u1, u4} m n α)) (Pi.instSMul.{u3, max (max u2 u1) u4, u5} o R (fun (k : o) => Matrix.{u2, u1, u4} m n α) (fun (i : o) => Matrix.smul.{u4, u2, u1, u5} m n R α (SMulZeroClass.toSMul.{u5, u4} R α (AddMonoid.toZero.{u4} α _inst_2) (DistribSMul.toSMulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_2) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_1 _inst_2 _inst_3)))))) x (Matrix.blockDiag.{u2, u1, u3, u4} m n o α M))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag_smul Matrix.blockDiag_smulₓ'. -/
@[simp]
theorem blockDiag_smul {R : Type _} [Monoid R] [AddMonoid α] [DistribMulAction R α] (x : R)
    (M : Matrix (m × o) (n × o) α) : blockDiag (x • M) = x • blockDiag M :=
  rfl
#align matrix.block_diag_smul Matrix.blockDiag_smul

end BlockDiag

section BlockDiagonal'

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

#print Matrix.blockDiagonal' /-
/-- `matrix.block_diagonal' M` turns `M : Π i, matrix (m i) (n i) α` into a
`Σ i, m i`-by-`Σ i, n i` block matrix which has the entries of `M` along the diagonal
and zero elsewhere.

This is the dependently-typed version of `matrix.block_diagonal`. -/
def blockDiagonal' (M : ∀ i, Matrix (m' i) (n' i) α) : Matrix (Σi, m' i) (Σi, n' i) α :=
  of <|
    (fun ⟨k, i⟩ ⟨k', j⟩ => if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0 :
      (Σi, m' i) → (Σi, n' i) → α)
#align matrix.block_diagonal' Matrix.blockDiagonal'
-/

/- warning: matrix.block_diagonal'_apply' -> Matrix.blockDiagonal'_apply' is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u4} α] (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (k : o) (i : m' k) (k' : o) (j : n' k'), Eq.{succ u4} α (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Sigma.mk.{u1, u2} o (fun (i : o) => m' i) k i) (Sigma.mk.{u1, u3} o (fun (i : o) => n' i) k' j)) (dite.{succ u4} α (Eq.{succ u1} o k k') (_inst_1 k k') (fun (h : Eq.{succ u1} o k k') => M k i (cast.{succ u3} (n' k') (n' k) (congr_arg.{succ u1, succ (succ u3)} o Type.{u3} k' k n' (Eq.symm.{succ u1} o k k' h)) j)) (fun (h : Not (Eq.{succ u1} o k k')) => OfNat.ofNat.{u4} α 0 (OfNat.mk.{u4} α 0 (Zero.zero.{u4} α _inst_2))))
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u4}} {n' : o -> Type.{u3}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : forall (i : o), Matrix.{u4, u3, u2} (m' i) (n' i) α) (k : o) (i : m' k) (k' : o) (j : n' k'), Eq.{succ u2} α (Matrix.blockDiagonal'.{u1, u4, u3, u2} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Sigma.mk.{u1, u4} o (fun (i : o) => m' i) k i) (Sigma.mk.{u1, u3} o (fun (i : o) => n' i) k' j)) (dite.{succ u2} α (Eq.{succ u1} o k k') (_inst_1 k k') (fun (h : Eq.{succ u1} o k k') => M k i (cast.{succ u3} (n' k') (n' k) (congr_arg.{succ u1, succ (succ u3)} o Type.{u3} k' k n' (Eq.symm.{succ u1} o k k' h)) j)) (fun (h : Not (Eq.{succ u1} o k k')) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_apply' Matrix.blockDiagonal'_apply'ₓ'. -/
-- TODO: set as an equation lemma for `block_diagonal'`, see mathlib4#3024
theorem blockDiagonal'_apply' (M : ∀ i, Matrix (m' i) (n' i) α) (k i k' j) :
    blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ =
      if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0 :=
  rfl
#align matrix.block_diagonal'_apply' Matrix.blockDiagonal'_apply'

/- warning: matrix.block_diagonal'_eq_block_diagonal -> Matrix.blockDiagonal'_eq_blockDiagonal is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : Zero.{u4} α] (M : o -> (Matrix.{u1, u2, u4} m n α)) {k : o} {k' : o} (i : m) (j : n), Eq.{succ u4} α (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Prod.mk.{u1, u3} m o i k) (Prod.mk.{u2, u3} n o j k')) (Matrix.blockDiagonal'.{u3, u1, u2, u4} o (fun (ᾰ : o) => m) (fun (ᾰ : o) => n) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Sigma.mk.{u3, u1} o (fun (i : o) => m) k i) (Sigma.mk.{u3, u2} o (fun (i : o) => n) k' j))
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : o -> (Matrix.{u4, u3, u2} m n α)) {k : o} {k' : o} (i : m) (j : n), Eq.{succ u2} α (Matrix.blockDiagonal.{u4, u3, u1, u2} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Prod.mk.{u4, u1} m o i k) (Prod.mk.{u3, u1} n o j k')) (Matrix.blockDiagonal'.{u1, u4, u3, u2} o (fun (ᾰ : o) => m) (fun (ᾰ : o) => n) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Sigma.mk.{u1, u4} o (fun (i : o) => m) k i) (Sigma.mk.{u1, u3} o (fun (i : o) => n) k' j))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_eq_block_diagonal Matrix.blockDiagonal'_eq_blockDiagonalₓ'. -/
theorem blockDiagonal'_eq_blockDiagonal (M : o → Matrix m n α) {k k'} (i j) :
    blockDiagonal M (i, k) (j, k') = blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ :=
  rfl
#align matrix.block_diagonal'_eq_block_diagonal Matrix.blockDiagonal'_eq_blockDiagonal

/- warning: matrix.block_diagonal'_submatrix_eq_block_diagonal -> Matrix.blockDiagonal'_submatrix_eq_blockDiagonal is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : Zero.{u4} α] (M : o -> (Matrix.{u1, u2, u4} m n α)), Eq.{succ (max (max u1 u3) (max u2 u3) u4)} (Matrix.{max u1 u3, max u2 u3, u4} (Prod.{u1, u3} m o) (Prod.{u2, u3} n o) α) (Matrix.submatrix.{u4, max u1 u3, max u3 u1, max u3 u2, max u2 u3} (Prod.{u1, u3} m o) (Sigma.{u3, u1} o (fun (i : o) => m)) (Sigma.{u3, u2} o (fun (i : o) => n)) (Prod.{u2, u3} n o) α (Matrix.blockDiagonal'.{u3, u1, u2, u4} o (fun (ᾰ : o) => m) (fun (ᾰ : o) => n) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M) (Function.comp.{succ (max u1 u3), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Prod.{u1, u3} m o) (Prod.{u3, u1} o m) (Sigma.{u3, u1} o (fun (i : o) => m)) (Prod.toSigma.{u3, u1} o m) (Prod.swap.{u1, u3} m o)) (Function.comp.{succ (max u2 u3), max (succ u3) (succ u2), max (succ u3) (succ u2)} (Prod.{u2, u3} n o) (Prod.{u3, u2} o n) (Sigma.{u3, u2} o (fun (i : o) => n)) (Prod.toSigma.{u3, u2} o n) (Prod.swap.{u2, u3} n o))) (Matrix.blockDiagonal.{u1, u2, u3, u4} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M)
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : o -> (Matrix.{u4, u3, u2} m n α)), Eq.{max (max (max (succ u4) (succ u3)) (succ u1)) (succ u2)} (Matrix.{max u1 u4, max u1 u3, u2} (Prod.{u4, u1} m o) (Prod.{u3, u1} n o) α) (Matrix.submatrix.{u2, max u1 u4, max u4 u1, max u3 u1, max u1 u3} (Prod.{u4, u1} m o) (Sigma.{u1, u4} o (fun (i : o) => m)) (Sigma.{u1, u3} o (fun (i : o) => n)) (Prod.{u3, u1} n o) α (Matrix.blockDiagonal'.{u1, u4, u3, u2} o (fun (ᾰ : o) => m) (fun (ᾰ : o) => n) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M) (Function.comp.{succ (max u1 u4), max (succ u4) (succ u1), max (succ u4) (succ u1)} (Prod.{u4, u1} m o) (Prod.{u1, u4} o m) (Sigma.{u1, u4} o (fun (i : o) => m)) (Prod.toSigma.{u1, u4} o m) (Prod.swap.{u4, u1} m o)) (Function.comp.{succ (max u1 u3), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Prod.{u3, u1} n o) (Prod.{u1, u3} o n) (Sigma.{u1, u3} o (fun (i : o) => n)) (Prod.toSigma.{u1, u3} o n) (Prod.swap.{u3, u1} n o))) (Matrix.blockDiagonal.{u4, u3, u1, u2} m n o α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M)
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_submatrix_eq_block_diagonal Matrix.blockDiagonal'_submatrix_eq_blockDiagonalₓ'. -/
theorem blockDiagonal'_submatrix_eq_blockDiagonal (M : o → Matrix m n α) :
    (blockDiagonal' M).submatrix (Prod.toSigma ∘ Prod.swap) (Prod.toSigma ∘ Prod.swap) =
      blockDiagonal M :=
  Matrix.ext fun ⟨k, i⟩ ⟨k', j⟩ => rfl
#align matrix.block_diagonal'_submatrix_eq_block_diagonal Matrix.blockDiagonal'_submatrix_eq_blockDiagonal

/- warning: matrix.block_diagonal'_apply -> Matrix.blockDiagonal'_apply is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u4} α] (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (ik : Sigma.{u1, u2} o (fun (i : o) => m' i)) (jk : Sigma.{u1, u3} o (fun (i : o) => n' i)), Eq.{succ u4} α (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M ik jk) (dite.{succ u4} α (Eq.{succ u1} o (Sigma.fst.{u1, u2} o (fun (i : o) => m' i) ik) (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk)) (_inst_1 (Sigma.fst.{u1, u2} o (fun (i : o) => m' i) ik) (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk)) (fun (h : Eq.{succ u1} o (Sigma.fst.{u1, u2} o (fun (i : o) => m' i) ik) (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk)) => M (Sigma.fst.{u1, u2} o (fun (i : o) => m' i) ik) (Sigma.snd.{u1, u2} o (fun (i : o) => m' i) ik) (cast.{succ u3} (n' (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk)) (n' (Sigma.fst.{u1, u2} o (fun (i : o) => m' i) ik)) (congr_arg.{succ u1, succ (succ u3)} o Type.{u3} (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk) (Sigma.fst.{u1, u2} o (fun (i : o) => m' i) ik) n' (Eq.symm.{succ u1} o (Sigma.fst.{u1, u2} o (fun (i : o) => m' i) ik) (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk) h)) (Sigma.snd.{u1, u3} o (fun (i : o) => n' i) jk))) (fun (h : Not (Eq.{succ u1} o (Sigma.fst.{u1, u2} o (fun (i : o) => m' i) ik) (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk))) => OfNat.ofNat.{u4} α 0 (OfNat.mk.{u4} α 0 (Zero.zero.{u4} α _inst_2))))
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u4}} {n' : o -> Type.{u3}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : forall (i : o), Matrix.{u4, u3, u2} (m' i) (n' i) α) (ik : Sigma.{u1, u4} o (fun (i : o) => m' i)) (jk : Sigma.{u1, u3} o (fun (i : o) => n' i)), Eq.{succ u2} α (Matrix.blockDiagonal'.{u1, u4, u3, u2} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M ik jk) (dite.{succ u2} α (Eq.{succ u1} o (Sigma.fst.{u1, u4} o (fun (i : o) => m' i) ik) (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk)) (_inst_1 (Sigma.fst.{u1, u4} o (fun (i : o) => m' i) ik) (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk)) (fun (h : Eq.{succ u1} o (Sigma.fst.{u1, u4} o (fun (i : o) => m' i) ik) (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk)) => M (Sigma.fst.{u1, u4} o (fun (i : o) => m' i) ik) (Sigma.snd.{u1, u4} o (fun (i : o) => m' i) ik) (cast.{succ u3} (n' (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk)) (n' (Sigma.fst.{u1, u4} o (fun (i : o) => m' i) ik)) (congr_arg.{succ u1, succ (succ u3)} o Type.{u3} (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk) (Sigma.fst.{u1, u4} o (fun (i : o) => m' i) ik) n' (Eq.symm.{succ u1} o (Sigma.fst.{u1, u4} o (fun (i : o) => m' i) ik) (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk) h)) (Sigma.snd.{u1, u3} o (fun (i : o) => n' i) jk))) (fun (h : Not (Eq.{succ u1} o (Sigma.fst.{u1, u4} o (fun (i : o) => m' i) ik) (Sigma.fst.{u1, u3} o (fun (i : o) => n' i) jk))) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_apply Matrix.blockDiagonal'_applyₓ'. -/
theorem blockDiagonal'_apply (M : ∀ i, Matrix (m' i) (n' i) α) (ik jk) :
    blockDiagonal' M ik jk =
      if h : ik.1 = jk.1 then M ik.1 ik.2 (cast (congr_arg n' h.symm) jk.2) else 0 :=
  by cases ik; cases jk; rfl
#align matrix.block_diagonal'_apply Matrix.blockDiagonal'_apply

/- warning: matrix.block_diagonal'_apply_eq -> Matrix.blockDiagonal'_apply_eq is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u4} α] (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (k : o) (i : m' k) (j : n' k), Eq.{succ u4} α (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Sigma.mk.{u1, u2} o (fun (i : o) => m' i) k i) (Sigma.mk.{u1, u3} o (fun (i : o) => n' i) k j)) (M k i j)
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u4}} {n' : o -> Type.{u3}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : forall (i : o), Matrix.{u4, u3, u2} (m' i) (n' i) α) (k : o) (i : m' k) (j : n' k), Eq.{succ u2} α (Matrix.blockDiagonal'.{u1, u4, u3, u2} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Sigma.mk.{u1, u4} o (fun (i : o) => m' i) k i) (Sigma.mk.{u1, u3} o (fun (i : o) => n' i) k j)) (M k i j)
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_apply_eq Matrix.blockDiagonal'_apply_eqₓ'. -/
@[simp]
theorem blockDiagonal'_apply_eq (M : ∀ i, Matrix (m' i) (n' i) α) (k i j) :
    blockDiagonal' M ⟨k, i⟩ ⟨k, j⟩ = M k i j :=
  dif_pos rfl
#align matrix.block_diagonal'_apply_eq Matrix.blockDiagonal'_apply_eq

/- warning: matrix.block_diagonal'_apply_ne -> Matrix.blockDiagonal'_apply_ne is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u4} α] (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) {k : o} {k' : o} (i : m' k) (j : n' k'), (Ne.{succ u1} o k k') -> (Eq.{succ u4} α (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Sigma.mk.{u1, u2} o (fun (i : o) => m' i) k i) (Sigma.mk.{u1, u3} o (fun (i : o) => n' i) k' j)) (OfNat.ofNat.{u4} α 0 (OfNat.mk.{u4} α 0 (Zero.zero.{u4} α _inst_2))))
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u4}} {n' : o -> Type.{u3}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : forall (i : o), Matrix.{u4, u3, u2} (m' i) (n' i) α) {k : o} {k' : o} (i : m' k) (j : n' k'), (Ne.{succ u1} o k k') -> (Eq.{succ u2} α (Matrix.blockDiagonal'.{u1, u4, u3, u2} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M (Sigma.mk.{u1, u4} o (fun (i : o) => m' i) k i) (Sigma.mk.{u1, u3} o (fun (i : o) => n' i) k' j)) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_apply_ne Matrix.blockDiagonal'_apply_neₓ'. -/
theorem blockDiagonal'_apply_ne (M : ∀ i, Matrix (m' i) (n' i) α) {k k'} (i j) (h : k ≠ k') :
    blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ = 0 :=
  dif_neg h
#align matrix.block_diagonal'_apply_ne Matrix.blockDiagonal'_apply_ne

/- warning: matrix.block_diagonal'_map -> Matrix.blockDiagonal'_map is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} {β : Type.{u5}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u4} α] [_inst_3 : Zero.{u5} β] (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (f : α -> β), (Eq.{succ u5} β (f (OfNat.ofNat.{u4} α 0 (OfNat.mk.{u4} α 0 (Zero.zero.{u4} α _inst_2)))) (OfNat.ofNat.{u5} β 0 (OfNat.mk.{u5} β 0 (Zero.zero.{u5} β _inst_3)))) -> (Eq.{succ (max (max u1 u2) (max u1 u3) u5)} (Matrix.{max u1 u2, max u1 u3, u5} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) β) (Matrix.map.{u4, u5, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α β (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M) f) (Matrix.blockDiagonal'.{u1, u2, u3, u5} o (fun (i : o) => m' i) (fun (i : o) => n' i) β (fun (a : o) (b : o) => _inst_1 a b) _inst_3 (fun (k : o) => Matrix.map.{u4, u5, u2, u3} (m' k) (n' k) α β (M k) f)))
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u5}} {n' : o -> Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u3} α] [_inst_3 : Zero.{u2} β] (M : forall (i : o), Matrix.{u5, u4, u3} (m' i) (n' i) α) (f : α -> β), (Eq.{succ u2} β (f (OfNat.ofNat.{u3} α 0 (Zero.toOfNat0.{u3} α _inst_2))) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_3))) -> (Eq.{max (max (max (succ u1) (succ u5)) (succ u4)) (succ u2)} (Matrix.{max u1 u5, max u1 u4, u2} (Sigma.{u1, u5} o (fun (i : o) => m' i)) (Sigma.{u1, u4} o (fun (i : o) => n' i)) β) (Matrix.map.{u3, u2, max u1 u5, max u1 u4} (Sigma.{u1, u5} o (fun (i : o) => m' i)) (Sigma.{u1, u4} o (fun (i : o) => n' i)) α β (Matrix.blockDiagonal'.{u1, u5, u4, u3} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M) f) (Matrix.blockDiagonal'.{u1, u5, u4, u2} o (fun (i : o) => m' i) (fun (i : o) => n' i) β (fun (a : o) (b : o) => _inst_1 a b) _inst_3 (fun (k : o) => Matrix.map.{u3, u2, u5, u4} (m' k) (n' k) α β (M k) f)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_map Matrix.blockDiagonal'_mapₓ'. -/
theorem blockDiagonal'_map (M : ∀ i, Matrix (m' i) (n' i) α) (f : α → β) (hf : f 0 = 0) :
    (blockDiagonal' M).map f = blockDiagonal' fun k => (M k).map f :=
  by
  ext
  simp only [map_apply, block_diagonal'_apply, eq_comm]
  rw [apply_dite f, hf]
#align matrix.block_diagonal'_map Matrix.blockDiagonal'_map

/- warning: matrix.block_diagonal'_transpose -> Matrix.blockDiagonal'_transpose is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u4} α] (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α), Eq.{succ (max (max u1 u3) (max u1 u2) u4)} (Matrix.{max u1 u3, max u1 u2, u4} (Sigma.{u1, u3} o (fun (i : o) => n' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) (Matrix.transpose.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M)) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => n' i) (fun (i : o) => m' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (fun (k : o) => Matrix.transpose.{u4, u2, u3} (m' k) (n' k) α (M k)))
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u4}} {n' : o -> Type.{u3}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] (M : forall (i : o), Matrix.{u4, u3, u2} (m' i) (n' i) α), Eq.{max (max (max (succ u1) (succ u4)) (succ u3)) (succ u2)} (Matrix.{max u3 u1, max u4 u1, u2} (Sigma.{u1, u3} o (fun (i : o) => n' i)) (Sigma.{u1, u4} o (fun (i : o) => m' i)) α) (Matrix.transpose.{u2, max u4 u1, max u3 u1} (Sigma.{u1, u4} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α (Matrix.blockDiagonal'.{u1, u4, u3, u2} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 M)) (Matrix.blockDiagonal'.{u1, u3, u4, u2} o (fun (i : o) => n' i) (fun (i : o) => m' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (fun (k : o) => Matrix.transpose.{u2, u4, u3} (m' k) (n' k) α (M k)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_transpose Matrix.blockDiagonal'_transposeₓ'. -/
@[simp]
theorem blockDiagonal'_transpose (M : ∀ i, Matrix (m' i) (n' i) α) :
    (blockDiagonal' M)ᵀ = blockDiagonal' fun k => (M k)ᵀ :=
  by
  ext (⟨ii, ix⟩⟨ji, jx⟩)
  simp only [transpose_apply, block_diagonal'_apply]
  split_ifs <;> cc
#align matrix.block_diagonal'_transpose Matrix.blockDiagonal'_transpose

/- warning: matrix.block_diagonal'_conj_transpose -> Matrix.blockDiagonal'_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} [_inst_1 : DecidableEq.{succ u1} o] {α : Type.{u4}} [_inst_4 : AddMonoid.{u4} α] [_inst_5 : StarAddMonoid.{u4} α _inst_4] (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α), Eq.{succ (max (max u1 u3) (max u1 u2) u4)} (Matrix.{max u1 u3, max u1 u2, u4} (Sigma.{u1, u3} o (fun (i : o) => n' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) (Matrix.conjTranspose.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α (InvolutiveStar.toHasStar.{u4} α (StarAddMonoid.toHasInvolutiveStar.{u4} α _inst_4 _inst_5)) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_4)) M)) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => n' i) (fun (i : o) => m' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_4)) (fun (k : o) => Matrix.conjTranspose.{u4, u2, u3} (m' k) (n' k) α (InvolutiveStar.toHasStar.{u4} α (StarAddMonoid.toHasInvolutiveStar.{u4} α _inst_4 _inst_5)) (M k)))
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u3}} {n' : o -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] {α : Type.{u4}} [_inst_4 : AddMonoid.{u4} α] [_inst_5 : StarAddMonoid.{u4} α _inst_4] (M : forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α), Eq.{max (max (max (succ u1) (succ u3)) (succ u2)) (succ u4)} (Matrix.{max u2 u1, max u3 u1, u4} (Sigma.{u1, u2} o (fun (i : o) => n' i)) (Sigma.{u1, u3} o (fun (i : o) => m' i)) α) (Matrix.conjTranspose.{u4, max u3 u1, max u2 u1} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α _inst_4 _inst_5)) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddMonoid.toZero.{u4} α _inst_4) M)) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => n' i) (fun (i : o) => m' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddMonoid.toZero.{u4} α _inst_4) (fun (k : o) => Matrix.conjTranspose.{u4, u3, u2} (m' k) (n' k) α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α _inst_4 _inst_5)) (M k)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_conj_transpose Matrix.blockDiagonal'_conjTransposeₓ'. -/
@[simp]
theorem blockDiagonal'_conjTranspose {α} [AddMonoid α] [StarAddMonoid α]
    (M : ∀ i, Matrix (m' i) (n' i) α) : (blockDiagonal' M)ᴴ = blockDiagonal' fun k => (M k)ᴴ :=
  by
  simp only [conj_transpose, block_diagonal'_transpose]
  exact block_diagonal'_map _ star (star_zero α)
#align matrix.block_diagonal'_conj_transpose Matrix.blockDiagonal'_conjTranspose

/- warning: matrix.block_diagonal'_zero -> Matrix.blockDiagonal'_zero is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u4} α], Eq.{succ (max (max u1 u2) (max u1 u3) u4)} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (OfNat.ofNat.{max u1 u2 u3 u4} (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) 0 (OfNat.mk.{max u1 u2 u3 u4} (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) 0 (Zero.zero.{max u1 u2 u3 u4} (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (Pi.instZero.{u1, max u2 u3 u4} o (fun (i : o) => Matrix.{u2, u3, u4} (m' i) (n' i) α) (fun (i : o) => Matrix.hasZero.{u4, u2, u3} (m' i) (n' i) α _inst_2)))))) (OfNat.ofNat.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) 0 (OfNat.mk.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) 0 (Zero.zero.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.hasZero.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α _inst_2))))
but is expected to have type
  forall {o : Type.{u4}} {m' : o -> Type.{u3}} {n' : o -> Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u4} o] [_inst_2 : Zero.{u1} α], Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (Matrix.{max u3 u4, max u2 u4, u1} (Sigma.{u4, u3} o (fun (i : o) => m' i)) (Sigma.{u4, u2} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u4, u3, u2, u1} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (OfNat.ofNat.{max (max (max u4 u3) u2) u1} (forall (i : o), Matrix.{u3, u2, u1} (m' i) (n' i) α) 0 (Zero.toOfNat0.{max (max (max u4 u3) u2) u1} (forall (i : o), Matrix.{u3, u2, u1} (m' i) (n' i) α) (Pi.instZero.{u4, max (max u3 u2) u1} o (fun (i : o) => Matrix.{u3, u2, u1} (m' i) (n' i) α) (fun (i : o) => Matrix.zero.{u1, u3, u2} (m' i) (n' i) α _inst_2))))) (OfNat.ofNat.{max (max (max u4 u3) u2) u1} (Matrix.{max u3 u4, max u2 u4, u1} (Sigma.{u4, u3} o (fun (i : o) => m' i)) (Sigma.{u4, u2} o (fun (i : o) => n' i)) α) 0 (Zero.toOfNat0.{max (max (max u4 u3) u2) u1} (Matrix.{max u3 u4, max u2 u4, u1} (Sigma.{u4, u3} o (fun (i : o) => m' i)) (Sigma.{u4, u2} o (fun (i : o) => n' i)) α) (Matrix.zero.{u1, max u4 u3, max u4 u2} (Sigma.{u4, u3} o (fun (i : o) => m' i)) (Sigma.{u4, u2} o (fun (i : o) => n' i)) α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_zero Matrix.blockDiagonal'_zeroₓ'. -/
@[simp]
theorem blockDiagonal'_zero : blockDiagonal' (0 : ∀ i, Matrix (m' i) (n' i) α) = 0 := by ext;
  simp [block_diagonal'_apply]
#align matrix.block_diagonal'_zero Matrix.blockDiagonal'_zero

/- warning: matrix.block_diagonal'_diagonal -> Matrix.blockDiagonal'_diagonal is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u3} α] [_inst_4 : forall (i : o), DecidableEq.{succ u2} (m' i)] (d : forall (i : o), (m' i) -> α), Eq.{succ (max (max u1 u2) u3)} (Matrix.{max u1 u2, max u1 u2, u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) (Matrix.blockDiagonal'.{u1, u2, u2, u3} o (fun (k : o) => m' k) (fun (k : o) => m' k) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (fun (k : o) => Matrix.diagonal.{u3, u2} (m' k) α (fun (a : m' k) (b : m' k) => _inst_4 k a b) _inst_2 (d k))) (Matrix.diagonal.{u3, max u1 u2} (Sigma.{u1, u2} o (fun (i : o) => m' i)) α (fun (a : Sigma.{u1, u2} o (fun (i : o) => m' i)) (b : Sigma.{u1, u2} o (fun (i : o) => m' i)) => Sigma.decidableEq.{u1, u2} o (fun (i : o) => m' i) (fun (a : o) (b : o) => _inst_1 a b) (fun (a : o) (a_1 : m' a) (b : m' a) => _inst_4 a a_1 b) a b) _inst_2 (fun (ik : Sigma.{u1, u2} o (fun (i : o) => m' i)) => d (Sigma.fst.{u1, u2} o (fun (i : o) => m' i) ik) (Sigma.snd.{u1, u2} o (fun (i : o) => m' i) ik)))
but is expected to have type
  forall {o : Type.{u2}} {m' : o -> Type.{u3}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} o] [_inst_2 : Zero.{u1} α] [_inst_4 : forall (i : o), DecidableEq.{succ u3} (m' i)] (d : forall (i : o), (m' i) -> α), Eq.{max (max (succ u2) (succ u3)) (succ u1)} (Matrix.{max u3 u2, max u3 u2, u1} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u3} o (fun (i : o) => m' i)) α) (Matrix.blockDiagonal'.{u2, u3, u3, u1} o (fun (k : o) => m' k) (fun (k : o) => m' k) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (fun (k : o) => Matrix.diagonal.{u1, u3} (m' k) α (fun (a : m' k) (b : m' k) => _inst_4 k a b) _inst_2 (d k))) (Matrix.diagonal.{u1, max u2 u3} (Sigma.{u2, u3} o (fun (i : o) => m' i)) α (fun (a : Sigma.{u2, u3} o (fun (i : o) => m' i)) (b : Sigma.{u2, u3} o (fun (i : o) => m' i)) => Sigma.instDecidableEqSigma.{u2, u3} o (fun (i : o) => m' i) (fun (a : o) (b : o) => _inst_1 a b) (fun (a : o) => (fun (a : o) (a_1 : m' a) (b : m' a) => _inst_4 a a_1 b) a) a b) _inst_2 (fun (ik : Sigma.{u2, u3} o (fun (i : o) => m' i)) => d (Sigma.fst.{u2, u3} o (fun (i : o) => m' i) ik) (Sigma.snd.{u2, u3} o (fun (i : o) => m' i) ik)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_diagonal Matrix.blockDiagonal'_diagonalₓ'. -/
@[simp]
theorem blockDiagonal'_diagonal [∀ i, DecidableEq (m' i)] (d : ∀ i, m' i → α) :
    (blockDiagonal' fun k => diagonal (d k)) = diagonal fun ik => d ik.1 ik.2 :=
  by
  ext (⟨i, k⟩⟨j, k'⟩)
  simp only [block_diagonal'_apply, diagonal]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp
  · simp [hij]
#align matrix.block_diagonal'_diagonal Matrix.blockDiagonal'_diagonal

/- warning: matrix.block_diagonal'_one -> Matrix.blockDiagonal'_one is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u3} α] [_inst_4 : forall (i : o), DecidableEq.{succ u2} (m' i)] [_inst_5 : One.{u3} α], Eq.{succ (max (max u1 u2) u3)} (Matrix.{max u1 u2, max u1 u2, u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) (Matrix.blockDiagonal'.{u1, u2, u2, u3} o (fun (i : o) => m' i) (fun (i : o) => m' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (OfNat.ofNat.{max u1 u2 u3} (forall (i : o), Matrix.{u2, u2, u3} (m' i) (m' i) α) 1 (OfNat.mk.{max u1 u2 u3} (forall (i : o), Matrix.{u2, u2, u3} (m' i) (m' i) α) 1 (One.one.{max u1 u2 u3} (forall (i : o), Matrix.{u2, u2, u3} (m' i) (m' i) α) (Pi.instOne.{u1, max u2 u3} o (fun (i : o) => Matrix.{u2, u2, u3} (m' i) (m' i) α) (fun (i : o) => Matrix.hasOne.{u3, u2} (m' i) α (fun (a : m' i) (b : m' i) => _inst_4 i a b) _inst_2 _inst_5)))))) (OfNat.ofNat.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) 1 (OfNat.mk.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) 1 (One.one.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) (Matrix.hasOne.{u3, max u1 u2} (Sigma.{u1, u2} o (fun (i : o) => m' i)) α (fun (a : Sigma.{u1, u2} o (fun (i : o) => m' i)) (b : Sigma.{u1, u2} o (fun (i : o) => m' i)) => Sigma.decidableEq.{u1, u2} o (fun (i : o) => m' i) (fun (a : o) (b : o) => _inst_1 a b) (fun (a : o) (a_1 : m' a) (b : m' a) => _inst_4 a a_1 b) a b) _inst_2 _inst_5))))
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u3}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : Zero.{u2} α] [_inst_4 : forall (i : o), DecidableEq.{succ u3} (m' i)] [_inst_5 : One.{u2} α], Eq.{max (max (succ u1) (succ u3)) (succ u2)} (Matrix.{max u3 u1, max u3 u1, u2} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => m' i)) α) (Matrix.blockDiagonal'.{u1, u3, u3, u2} o (fun (i : o) => m' i) (fun (i : o) => m' i) α (fun (a : o) (b : o) => _inst_1 a b) _inst_2 (OfNat.ofNat.{max (max u1 u3) u2} (forall (i : o), Matrix.{u3, u3, u2} (m' i) (m' i) α) 1 (One.toOfNat1.{max (max u1 u3) u2} (forall (i : o), Matrix.{u3, u3, u2} (m' i) (m' i) α) (Pi.instOne.{u1, max u3 u2} o (fun (i : o) => Matrix.{u3, u3, u2} (m' i) (m' i) α) (fun (i : o) => Matrix.one.{u2, u3} (m' i) α (fun (a : m' i) (b : m' i) => _inst_4 i a b) _inst_2 _inst_5))))) (OfNat.ofNat.{max (max u1 u3) u2} (Matrix.{max u3 u1, max u3 u1, u2} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => m' i)) α) 1 (One.toOfNat1.{max (max u1 u3) u2} (Matrix.{max u3 u1, max u3 u1, u2} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => m' i)) α) (Matrix.one.{u2, max u1 u3} (Sigma.{u1, u3} o (fun (i : o) => m' i)) α (fun (a : Sigma.{u1, u3} o (fun (i : o) => m' i)) (b : Sigma.{u1, u3} o (fun (i : o) => m' i)) => Sigma.instDecidableEqSigma.{u1, u3} o (fun (i : o) => m' i) (fun (a : o) (b : o) => _inst_1 a b) (fun (a : o) => (fun (a : o) (a_1 : m' a) (b : m' a) => _inst_4 a a_1 b) a) a b) _inst_2 _inst_5)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_one Matrix.blockDiagonal'_oneₓ'. -/
@[simp]
theorem blockDiagonal'_one [∀ i, DecidableEq (m' i)] [One α] :
    blockDiagonal' (1 : ∀ i, Matrix (m' i) (m' i) α) = 1 :=
  show (blockDiagonal' fun i : o => diagonal fun _ : m' i => (1 : α)) = diagonal fun _ => 1 by
    rw [block_diagonal'_diagonal]
#align matrix.block_diagonal'_one Matrix.blockDiagonal'_one

end Zero

/- warning: matrix.block_diagonal'_add -> Matrix.blockDiagonal'_add is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : AddZeroClass.{u4} α] (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (N : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α), Eq.{succ (max (max u1 u2) (max u1 u3) u4)} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α _inst_2) (HAdd.hAdd.{max u1 u2 u3 u4, max u1 u2 u3 u4, max u1 u2 u3 u4} (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (instHAdd.{max u1 u2 u3 u4} (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (Pi.instAdd.{u1, max u2 u3 u4} o (fun (i : o) => Matrix.{u2, u3, u4} (m' i) (n' i) α) (fun (i : o) => Matrix.hasAdd.{u4, u2, u3} (m' i) (n' i) α (AddZeroClass.toHasAdd.{u4} α _inst_2)))) M N)) (HAdd.hAdd.{max (max u1 u2) (max u1 u3) u4, max (max u1 u2) (max u1 u3) u4, max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (instHAdd.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.hasAdd.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α (AddZeroClass.toHasAdd.{u4} α _inst_2))) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α _inst_2) M) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α _inst_2) N))
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u3}} {n' : o -> Type.{u2}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : AddZeroClass.{u4} α] (M : forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (N : forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α), Eq.{max (max (max (succ u1) (succ u3)) (succ u2)) (succ u4)} (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toZero.{u4} α _inst_2) (HAdd.hAdd.{max (max (max u1 u3) u2) u4, max (max (max u1 u3) u2) u4, max (max (max u1 u3) u2) u4} (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (instHAdd.{max (max (max u1 u3) u2) u4} (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (Pi.instAdd.{u1, max (max u3 u2) u4} o (fun (i : o) => Matrix.{u3, u2, u4} (m' i) (n' i) α) (fun (i : o) => Matrix.add.{u4, u3, u2} (m' i) (n' i) α (AddZeroClass.toAdd.{u4} α _inst_2)))) M N)) (HAdd.hAdd.{max (max (max u1 u3) u2) u4, max (max (max u1 u3) u2) u4, max (max (max u1 u3) u2) u4} (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (instHAdd.{max (max (max u1 u3) u2) u4} (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.add.{u4, max u1 u3, max u1 u2} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α (AddZeroClass.toAdd.{u4} α _inst_2))) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toZero.{u4} α _inst_2) M) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toZero.{u4} α _inst_2) N))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_add Matrix.blockDiagonal'_addₓ'. -/
@[simp]
theorem blockDiagonal'_add [AddZeroClass α] (M N : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (M + N) = blockDiagonal' M + blockDiagonal' N :=
  by
  ext
  simp only [block_diagonal'_apply, Pi.add_apply]
  split_ifs <;> simp
#align matrix.block_diagonal'_add Matrix.blockDiagonal'_add

section

variable (m' n' α)

#print Matrix.blockDiagonal'AddMonoidHom /-
/-- `matrix.block_diagonal'` as an `add_monoid_hom`. -/
@[simps]
def blockDiagonal'AddMonoidHom [AddZeroClass α] :
    (∀ i, Matrix (m' i) (n' i) α) →+ Matrix (Σi, m' i) (Σi, n' i) α
    where
  toFun := blockDiagonal'
  map_zero' := blockDiagonal'_zero
  map_add' := blockDiagonal'_add
#align matrix.block_diagonal'_add_monoid_hom Matrix.blockDiagonal'AddMonoidHom
-/

end

/- warning: matrix.block_diagonal'_neg -> Matrix.blockDiagonal'_neg is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : AddGroup.{u4} α] (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α), Eq.{succ (max (max u1 u2) (max u1 u3) u4)} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) (Neg.neg.{max u1 u2 u3 u4} (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (Pi.instNeg.{u1, max u2 u3 u4} o (fun (i : o) => Matrix.{u2, u3, u4} (m' i) (n' i) α) (fun (i : o) => Matrix.hasNeg.{u4, u2, u3} (m' i) (n' i) α (SubNegMonoid.toHasNeg.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) M)) (Neg.neg.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.hasNeg.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α (SubNegMonoid.toHasNeg.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2))) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) M))
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u3}} {n' : o -> Type.{u2}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : AddGroup.{u4} α] (M : forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α), Eq.{max (max (max (succ u1) (succ u3)) (succ u2)) (succ u4)} (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))) (Neg.neg.{max (max (max u1 u3) u2) u4} (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (Pi.instNeg.{u1, max (max u3 u2) u4} o (fun (i : o) => Matrix.{u3, u2, u4} (m' i) (n' i) α) (fun (i : o) => Matrix.neg.{u4, u3, u2} (m' i) (n' i) α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))))) M)) (Neg.neg.{max (max (max u1 u3) u2) u4} (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.neg.{u4, max u1 u3, max u1 u2} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2))))) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))) M))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_neg Matrix.blockDiagonal'_negₓ'. -/
@[simp]
theorem blockDiagonal'_neg [AddGroup α] (M : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (-M) = -blockDiagonal' M :=
  map_neg (blockDiagonal'AddMonoidHom m' n' α) M
#align matrix.block_diagonal'_neg Matrix.blockDiagonal'_neg

/- warning: matrix.block_diagonal'_sub -> Matrix.blockDiagonal'_sub is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : AddGroup.{u4} α] (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (N : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α), Eq.{succ (max (max u1 u2) (max u1 u3) u4)} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) (HSub.hSub.{max u1 u2 u3 u4, max u1 u2 u3 u4, max u1 u2 u3 u4} (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (instHSub.{max u1 u2 u3 u4} (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (Pi.instSub.{u1, max u2 u3 u4} o (fun (i : o) => Matrix.{u2, u3, u4} (m' i) (n' i) α) (fun (i : o) => Matrix.hasSub.{u4, u2, u3} (m' i) (n' i) α (SubNegMonoid.toHasSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2))))) M N)) (HSub.hSub.{max (max u1 u2) (max u1 u3) u4, max (max u1 u2) (max u1 u3) u4, max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (instHSub.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.hasSub.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α (SubNegMonoid.toHasSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) M) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) N))
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u3}} {n' : o -> Type.{u2}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : AddGroup.{u4} α] (M : forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (N : forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α), Eq.{max (max (max (succ u1) (succ u3)) (succ u2)) (succ u4)} (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))) (HSub.hSub.{max (max (max u1 u3) u2) u4, max (max (max u1 u3) u2) u4, max (max (max u1 u3) u2) u4} (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (instHSub.{max (max (max u1 u3) u2) u4} (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (Pi.instSub.{u1, max (max u3 u2) u4} o (fun (i : o) => Matrix.{u3, u2, u4} (m' i) (n' i) α) (fun (i : o) => Matrix.sub.{u4, u3, u2} (m' i) (n' i) α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2))))) M N)) (HSub.hSub.{max (max (max u1 u3) u2) u4, max (max (max u1 u3) u2) u4, max (max (max u1 u3) u2) u4} (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (instHSub.{max (max (max u1 u3) u2) u4} (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.sub.{u4, max u1 u3, max u1 u2} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_2)))) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))) M) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_2)))) N))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_sub Matrix.blockDiagonal'_subₓ'. -/
@[simp]
theorem blockDiagonal'_sub [AddGroup α] (M N : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (M - N) = blockDiagonal' M - blockDiagonal' N :=
  map_sub (blockDiagonal'AddMonoidHom m' n' α) M N
#align matrix.block_diagonal'_sub Matrix.blockDiagonal'_sub

/- warning: matrix.block_diagonal'_mul -> Matrix.blockDiagonal'_mul is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {p' : o -> Type.{u4}} {α : Type.{u5}} [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : NonUnitalNonAssocSemiring.{u5} α] [_inst_3 : forall (i : o), Fintype.{u3} (n' i)] [_inst_4 : Fintype.{u1} o] (M : forall (i : o), Matrix.{u2, u3, u5} (m' i) (n' i) α) (N : forall (i : o), Matrix.{u3, u4, u5} (n' i) (p' i) α), Eq.{succ (max (max u1 u2) (max u1 u4) u5)} (Matrix.{max u1 u2, max u1 u4, u5} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u4} o (fun (i : o) => p' i)) α) (Matrix.blockDiagonal'.{u1, u2, u4, u5} o (fun (k : o) => m' k) (fun (k : o) => p' k) α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toHasZero.{u5} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u5} α _inst_2)) (fun (k : o) => Matrix.mul.{u5, u2, u3, u4} (m' k) (n' k) (p' k) α (_inst_3 k) (Distrib.toHasMul.{u5} α (NonUnitalNonAssocSemiring.toDistrib.{u5} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α _inst_2) (M k) (N k))) (Matrix.mul.{u5, max u1 u2, max u1 u3, max u1 u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) (Sigma.{u1, u4} o (fun (i : o) => p' i)) α (Sigma.fintype.{u1, u3} o (fun (i : o) => n' i) _inst_4 (fun (a : o) => _inst_3 a)) (Distrib.toHasMul.{u5} α (NonUnitalNonAssocSemiring.toDistrib.{u5} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α _inst_2) (Matrix.blockDiagonal'.{u1, u2, u3, u5} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toHasZero.{u5} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u5} α _inst_2)) M) (Matrix.blockDiagonal'.{u1, u3, u4, u5} o (fun (i : o) => n' i) (fun (i : o) => p' i) α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toHasZero.{u5} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u5} α _inst_2)) N))
but is expected to have type
  forall {o : Type.{u3}} {m' : o -> Type.{u2}} {n' : o -> Type.{u4}} {p' : o -> Type.{u1}} {α : Type.{u5}} [_inst_1 : DecidableEq.{succ u3} o] [_inst_2 : NonUnitalNonAssocSemiring.{u5} α] [_inst_3 : forall (i : o), Fintype.{u4} (n' i)] [_inst_4 : Fintype.{u3} o] (M : forall (i : o), Matrix.{u2, u4, u5} (m' i) (n' i) α) (N : forall (i : o), Matrix.{u4, u1, u5} (n' i) (p' i) α), Eq.{max (max (max (succ u3) (succ u2)) (succ u1)) (succ u5)} (Matrix.{max u2 u3, max u1 u3, u5} (Sigma.{u3, u2} o (fun (i : o) => m' i)) (Sigma.{u3, u1} o (fun (i : o) => p' i)) α) (Matrix.blockDiagonal'.{u3, u2, u1, u5} o (fun (k : o) => m' k) (fun (k : o) => p' k) α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toZero.{u5} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u5} α _inst_2)) (fun (k : o) => Matrix.mul.{u5, u2, u4, u1} (m' k) (n' k) (p' k) α (_inst_3 k) (NonUnitalNonAssocSemiring.toMul.{u5} α _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α _inst_2) (M k) (N k))) (Matrix.mul.{u5, max u2 u3, max u4 u3, max u3 u1} (Sigma.{u3, u2} o (fun (i : o) => m' i)) (Sigma.{u3, u4} o (fun (i : o) => n' i)) (Sigma.{u3, u1} o (fun (i : o) => p' i)) α (instFintypeSigma.{u3, u4} o (fun (i : o) => n' i) _inst_4 (fun (a : o) => _inst_3 a)) (NonUnitalNonAssocSemiring.toMul.{u5} α _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α _inst_2) (Matrix.blockDiagonal'.{u3, u2, u4, u5} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toZero.{u5} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u5} α _inst_2)) M) (Matrix.blockDiagonal'.{u3, u4, u1, u5} o (fun (i : o) => n' i) (fun (i : o) => p' i) α (fun (a : o) (b : o) => _inst_1 a b) (MulZeroClass.toZero.{u5} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u5} α _inst_2)) N))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_mul Matrix.blockDiagonal'_mulₓ'. -/
@[simp]
theorem blockDiagonal'_mul [NonUnitalNonAssocSemiring α] [∀ i, Fintype (n' i)] [Fintype o]
    (M : ∀ i, Matrix (m' i) (n' i) α) (N : ∀ i, Matrix (n' i) (p' i) α) :
    (blockDiagonal' fun k => M k ⬝ N k) = blockDiagonal' M ⬝ blockDiagonal' N :=
  by
  ext (⟨k, i⟩⟨k', j⟩)
  simp only [block_diagonal'_apply, mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · split_ifs <;> simp
  · intro j' hj';
    exact Finset.sum_eq_zero fun _ _ => by rw [dif_neg hj'.symm, MulZeroClass.zero_mul]
#align matrix.block_diagonal'_mul Matrix.blockDiagonal'_mul

section

variable (α m')

/- warning: matrix.block_diagonal'_ring_hom -> Matrix.blockDiagonal'RingHom is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} (m' : o -> Type.{u2}) (α : Type.{u3}) [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : forall (i : o), DecidableEq.{succ u2} (m' i)] [_inst_3 : Fintype.{u1} o] [_inst_4 : forall (i : o), Fintype.{u2} (m' i)] [_inst_5 : NonAssocSemiring.{u3} α], RingHom.{max u1 u2 u3, max (max u1 u2) u3} (forall (i : o), Matrix.{u2, u2, u3} (m' i) (m' i) α) (Matrix.{max u1 u2, max u1 u2, u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) (Pi.nonAssocSemiring.{u1, max u2 u3} o (fun (i : o) => Matrix.{u2, u2, u3} (m' i) (m' i) α) (fun (i : o) => Matrix.nonAssocSemiring.{u3, u2} (m' i) α _inst_5 (_inst_4 i) (fun (a : m' i) (b : m' i) => _inst_2 i a b))) (Matrix.nonAssocSemiring.{u3, max u1 u2} (Sigma.{u1, u2} o (fun (i : o) => m' i)) α _inst_5 (Sigma.fintype.{u1, u2} o (fun (i : o) => m' i) _inst_3 (fun (i : o) => _inst_4 i)) (fun (a : Sigma.{u1, u2} o (fun (i : o) => m' i)) (b : Sigma.{u1, u2} o (fun (i : o) => m' i)) => Sigma.decidableEq.{u1, u2} o (fun (i : o) => m' i) (fun (a : o) (b : o) => _inst_1 a b) (fun (a : o) (a_1 : m' a) (b : m' a) => _inst_2 a a_1 b) a b))
but is expected to have type
  forall {o : Type.{u1}} (m' : o -> Type.{u2}) (α : Type.{u3}) [_inst_1 : DecidableEq.{succ u1} o] [_inst_2 : forall (i : o), DecidableEq.{succ u2} (m' i)] [_inst_3 : Fintype.{u1} o] [_inst_4 : forall (i : o), Fintype.{u2} (m' i)] [_inst_5 : NonAssocSemiring.{u3} α], RingHom.{max (max u1 u2) u3, max u3 u2 u1} (forall (i : o), Matrix.{u2, u2, u3} (m' i) (m' i) α) (Matrix.{max u2 u1, max u2 u1, u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) (Pi.nonAssocSemiring.{u1, max u2 u3} o (fun (i : o) => Matrix.{u2, u2, u3} (m' i) (m' i) α) (fun (i : o) => Matrix.nonAssocSemiring.{u3, u2} (m' i) α _inst_5 (_inst_4 i) (fun (a : m' i) (b : m' i) => _inst_2 i a b))) (Matrix.nonAssocSemiring.{u3, max u1 u2} (Sigma.{u1, u2} o (fun (i : o) => m' i)) α _inst_5 (instFintypeSigma.{u1, u2} o (fun (i : o) => m' i) _inst_3 (fun (i : o) => _inst_4 i)) (fun (a : Sigma.{u1, u2} o (fun (i : o) => m' i)) (b : Sigma.{u1, u2} o (fun (i : o) => m' i)) => Sigma.instDecidableEqSigma.{u1, u2} o (fun (i : o) => m' i) (fun (a : o) (b : o) => _inst_1 a b) (fun (a : o) => (fun (a : o) (a_1 : m' a) (b : m' a) => _inst_2 a a_1 b) a) a b))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_ring_hom Matrix.blockDiagonal'RingHomₓ'. -/
/-- `matrix.block_diagonal'` as a `ring_hom`. -/
@[simps]
def blockDiagonal'RingHom [∀ i, DecidableEq (m' i)] [Fintype o] [∀ i, Fintype (m' i)]
    [NonAssocSemiring α] : (∀ i, Matrix (m' i) (m' i) α) →+* Matrix (Σi, m' i) (Σi, m' i) α :=
  {
    blockDiagonal'AddMonoidHom m' m'
      α with
    toFun := blockDiagonal'
    map_one' := blockDiagonal'_one
    map_mul' := blockDiagonal'_mul }
#align matrix.block_diagonal'_ring_hom Matrix.blockDiagonal'RingHom

end

/- warning: matrix.block_diagonal'_pow -> Matrix.blockDiagonal'_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_pow Matrix.blockDiagonal'_powₓ'. -/
@[simp]
theorem blockDiagonal'_pow [∀ i, DecidableEq (m' i)] [Fintype o] [∀ i, Fintype (m' i)] [Semiring α]
    (M : ∀ i, Matrix (m' i) (m' i) α) (n : ℕ) : blockDiagonal' (M ^ n) = blockDiagonal' M ^ n :=
  map_pow (blockDiagonal'RingHom m' α) M n
#align matrix.block_diagonal'_pow Matrix.blockDiagonal'_pow

/- warning: matrix.block_diagonal'_smul -> Matrix.blockDiagonal'_smul is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] {R : Type.{u5}} [_inst_2 : Semiring.{u5} R] [_inst_3 : AddCommMonoid.{u4} α] [_inst_4 : Module.{u5, u4} R α _inst_2 _inst_3] (x : R) (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α), Eq.{succ (max (max u1 u2) (max u1 u3) u4)} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3))) (SMul.smul.{u5, max u1 u2 u3 u4} R (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (Pi.instSMul.{u1, max u2 u3 u4, u5} o R (fun (i : o) => Matrix.{u2, u3, u4} (m' i) (n' i) α) (fun (i : o) => Matrix.hasSmul.{u4, u2, u3, u5} (m' i) (n' i) R α (SMulZeroClass.toHasSmul.{u5, u4} R α (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3))) (SMulWithZero.toSmulZeroClass.{u5, u4} R α (MulZeroClass.toHasZero.{u5} R (MulZeroOneClass.toMulZeroClass.{u5} R (MonoidWithZero.toMulZeroOneClass.{u5} R (Semiring.toMonoidWithZero.{u5} R _inst_2)))) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3))) (MulActionWithZero.toSMulWithZero.{u5, u4} R α (Semiring.toMonoidWithZero.{u5} R _inst_2) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3))) (Module.toMulActionWithZero.{u5, u4} R α _inst_2 _inst_3 _inst_4)))))) x M)) (SMul.smul.{u5, max (max u1 u2) (max u1 u3) u4} R (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.hasSmul.{u4, max u1 u2, max u1 u3, u5} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) R α (SMulZeroClass.toHasSmul.{u5, u4} R α (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3))) (SMulWithZero.toSmulZeroClass.{u5, u4} R α (MulZeroClass.toHasZero.{u5} R (MulZeroOneClass.toMulZeroClass.{u5} R (MonoidWithZero.toMulZeroOneClass.{u5} R (Semiring.toMonoidWithZero.{u5} R _inst_2)))) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3))) (MulActionWithZero.toSMulWithZero.{u5, u4} R α (Semiring.toMonoidWithZero.{u5} R _inst_2) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3))) (Module.toMulActionWithZero.{u5, u4} R α _inst_2 _inst_3 _inst_4))))) x (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3))) M))
but is expected to have type
  forall {o : Type.{u1}} {m' : o -> Type.{u3}} {n' : o -> Type.{u2}} {α : Type.{u4}} [_inst_1 : DecidableEq.{succ u1} o] {R : Type.{u5}} [_inst_2 : Semiring.{u5} R] [_inst_3 : AddCommMonoid.{u4} α] [_inst_4 : Module.{u5, u4} R α _inst_2 _inst_3] (x : R) (M : forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α), Eq.{max (max (max (succ u1) (succ u3)) (succ u2)) (succ u4)} (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)) (HSMul.hSMul.{u5, max (max (max u1 u3) u2) u4, max (max (max u1 u3) u2) u4} R (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (instHSMul.{u5, max (max (max u1 u3) u2) u4} R (forall (i : o), Matrix.{u3, u2, u4} (m' i) (n' i) α) (Pi.instSMul.{u1, max (max u3 u2) u4, u5} o R (fun (i : o) => Matrix.{u3, u2, u4} (m' i) (n' i) α) (fun (i : o) => Matrix.smul.{u4, u3, u2, u5} (m' i) (n' i) R α (SMulZeroClass.toSMul.{u5, u4} R α (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)) (SMulWithZero.toSMulZeroClass.{u5, u4} R α (MonoidWithZero.toZero.{u5} R (Semiring.toMonoidWithZero.{u5} R _inst_2)) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)) (MulActionWithZero.toSMulWithZero.{u5, u4} R α (Semiring.toMonoidWithZero.{u5} R _inst_2) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)) (Module.toMulActionWithZero.{u5, u4} R α _inst_2 _inst_3 _inst_4))))))) x M)) (HSMul.hSMul.{u5, max (max (max u4 u2) u3) u1, max (max (max u1 u3) u2) u4} R (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (instHSMul.{u5, max (max (max u1 u3) u2) u4} R (Matrix.{max u3 u1, max u2 u1, u4} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) α) (Matrix.smul.{u4, max u1 u3, max u1 u2, u5} (Sigma.{u1, u3} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => n' i)) R α (SMulZeroClass.toSMul.{u5, u4} R α (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)) (SMulWithZero.toSMulZeroClass.{u5, u4} R α (MonoidWithZero.toZero.{u5} R (Semiring.toMonoidWithZero.{u5} R _inst_2)) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)) (MulActionWithZero.toSMulWithZero.{u5, u4} R α (Semiring.toMonoidWithZero.{u5} R _inst_2) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)) (Module.toMulActionWithZero.{u5, u4} R α _inst_2 _inst_3 _inst_4)))))) x (Matrix.blockDiagonal'.{u1, u3, u2, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_1 a b) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)) M))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_smul Matrix.blockDiagonal'_smulₓ'. -/
@[simp]
theorem blockDiagonal'_smul {R : Type _} [Semiring R] [AddCommMonoid α] [Module R α] (x : R)
    (M : ∀ i, Matrix (m' i) (n' i) α) : blockDiagonal' (x • M) = x • blockDiagonal' M := by ext;
  simp only [block_diagonal'_apply, Pi.smul_apply]; split_ifs <;> simp
#align matrix.block_diagonal'_smul Matrix.blockDiagonal'_smul

end BlockDiagonal'

section BlockDiag'

#print Matrix.blockDiag' /-
/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `matrix.diag`, and the left-inverse of `matrix.block_diagonal'`. -/
def blockDiag' (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) : Matrix (m' k) (n' k) α :=
  of fun i j => M ⟨k, i⟩ ⟨k, j⟩
#align matrix.block_diag' Matrix.blockDiag'
-/

/- warning: matrix.block_diag'_apply -> Matrix.blockDiag'_apply is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} (M : Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (k : o) (i : m' k) (j : n' k), Eq.{succ u4} α (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α M k i j) (M (Sigma.mk.{u1, u2} o (fun (i : o) => m' i) k i) (Sigma.mk.{u1, u3} o (fun (i : o) => n' i) k j))
but is expected to have type
  forall {o : Type.{u3}} {m' : o -> Type.{u4}} {n' : o -> Type.{u2}} {α : Type.{u1}} (M : Matrix.{max u4 u3, max u2 u3, u1} (Sigma.{u3, u4} o (fun (i : o) => m' i)) (Sigma.{u3, u2} o (fun (i : o) => n' i)) α) (k : o) (i : m' k) (j : n' k), Eq.{succ u1} α (Matrix.blockDiag'.{u3, u4, u2, u1} o (fun (i : o) => m' i) (fun (i : o) => n' i) α M k i j) (M (Sigma.mk.{u3, u4} o (fun (i : o) => m' i) k i) (Sigma.mk.{u3, u2} o (fun (i : o) => n' i) k j))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_apply Matrix.blockDiag'_applyₓ'. -/
-- TODO: set as an equation lemma for `block_diag'`, see mathlib4#3024
theorem blockDiag'_apply (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) (i j) :
    blockDiag' M k i j = M ⟨k, i⟩ ⟨k, j⟩ :=
  rfl
#align matrix.block_diag'_apply Matrix.blockDiag'_apply

/- warning: matrix.block_diag'_map -> Matrix.blockDiag'_map is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} {β : Type.{u5}} (M : Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (f : α -> β), Eq.{max (succ u1) (succ (max u2 u3 u5))} (forall (k : o), Matrix.{u2, u3, u5} (m' k) (n' k) β) (Matrix.blockDiag'.{u1, u2, u3, u5} o (fun (i : o) => m' i) (fun (i : o) => n' i) β (Matrix.map.{u4, u5, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α β M f)) (fun (k : o) => Matrix.map.{u4, u5, u2, u3} (m' k) (n' k) α β (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α M k) f)
but is expected to have type
  forall {o : Type.{u4}} {m' : o -> Type.{u5}} {n' : o -> Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} (M : Matrix.{max u5 u4, max u3 u4, u2} (Sigma.{u4, u5} o (fun (i : o) => m' i)) (Sigma.{u4, u3} o (fun (i : o) => n' i)) α) (f : α -> β), Eq.{max (max (max (succ u4) (succ u5)) (succ u3)) (succ u1)} (forall (k : o), Matrix.{u5, u3, u1} (m' k) (n' k) β) (Matrix.blockDiag'.{u4, u5, u3, u1} o (fun (i : o) => m' i) (fun (i : o) => n' i) β (Matrix.map.{u2, u1, max u4 u5, max u4 u3} (Sigma.{u4, u5} o (fun (i : o) => m' i)) (Sigma.{u4, u3} o (fun (i : o) => n' i)) α β M f)) (fun (k : o) => Matrix.map.{u2, u1, u5, u3} (m' k) (n' k) α β (Matrix.blockDiag'.{u4, u5, u3, u2} o (fun (i : o) => m' i) (fun (i : o) => n' i) α M k) f)
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_map Matrix.blockDiag'_mapₓ'. -/
theorem blockDiag'_map (M : Matrix (Σi, m' i) (Σi, n' i) α) (f : α → β) :
    blockDiag' (M.map f) = fun k => (blockDiag' M k).map f :=
  rfl
#align matrix.block_diag'_map Matrix.blockDiag'_map

/- warning: matrix.block_diag'_transpose -> Matrix.blockDiag'_transpose is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} (M : Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (k : o), Eq.{succ (max u3 u2 u4)} (Matrix.{u3, u2, u4} (n' k) (m' k) α) (Matrix.blockDiag'.{u1, u3, u2, u4} o (fun (i : o) => n' i) (fun (i : o) => m' i) α (Matrix.transpose.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α M) k) (Matrix.transpose.{u4, u2, u3} (m' k) (n' k) α (Matrix.blockDiag'.{u1, u2, u3, u4} o m' (fun (k : o) => n' k) α M k))
but is expected to have type
  forall {o : Type.{u3}} {m' : o -> Type.{u4}} {n' : o -> Type.{u2}} {α : Type.{u1}} (M : Matrix.{max u4 u3, max u2 u3, u1} (Sigma.{u3, u4} o (fun (i : o) => m' i)) (Sigma.{u3, u2} o (fun (i : o) => n' i)) α) (k : o), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u4, u1} (n' k) (m' k) α) (Matrix.blockDiag'.{u3, u2, u4, u1} o (fun (i : o) => n' i) (fun (i : o) => m' i) α (Matrix.transpose.{u1, max u4 u3, max u2 u3} (Sigma.{u3, u4} o (fun (i : o) => m' i)) (Sigma.{u3, u2} o (fun (i : o) => n' i)) α M) k) (Matrix.transpose.{u1, u4, u2} (m' k) (n' k) α (Matrix.blockDiag'.{u3, u4, u2, u1} o (fun (i : o) => m' i) (fun (k : o) => n' k) α M k))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_transpose Matrix.blockDiag'_transposeₓ'. -/
@[simp]
theorem blockDiag'_transpose (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) :
    blockDiag' Mᵀ k = (blockDiag' M k)ᵀ :=
  ext fun i j => rfl
#align matrix.block_diag'_transpose Matrix.blockDiag'_transpose

/- warning: matrix.block_diag'_conj_transpose -> Matrix.blockDiag'_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : AddMonoid.{u4} α] [_inst_2 : StarAddMonoid.{u4} α _inst_1] (M : Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (k : o), Eq.{succ (max u3 u2 u4)} (Matrix.{u3, u2, u4} (n' k) (m' k) α) (Matrix.blockDiag'.{u1, u3, u2, u4} o (fun (i : o) => n' i) (fun (i : o) => m' i) α (Matrix.conjTranspose.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α (InvolutiveStar.toHasStar.{u4} α (StarAddMonoid.toHasInvolutiveStar.{u4} α _inst_1 _inst_2)) M) k) (Matrix.conjTranspose.{u4, u2, u3} (m' k) (n' k) α (InvolutiveStar.toHasStar.{u4} α (StarAddMonoid.toHasInvolutiveStar.{u4} α _inst_1 _inst_2)) (Matrix.blockDiag'.{u1, u2, u3, u4} o m' (fun (k : o) => n' k) α M k))
but is expected to have type
  forall {o : Type.{u2}} {m' : o -> Type.{u3}} {n' : o -> Type.{u1}} {α : Type.{u4}} [_inst_1 : AddMonoid.{u4} α] [_inst_2 : StarAddMonoid.{u4} α _inst_1] (M : Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (k : o), Eq.{max (max (succ u3) (succ u1)) (succ u4)} (Matrix.{u1, u3, u4} (n' k) (m' k) α) (Matrix.blockDiag'.{u2, u1, u3, u4} o (fun (i : o) => n' i) (fun (i : o) => m' i) α (Matrix.conjTranspose.{u4, max u3 u2, max u1 u2} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α _inst_1 _inst_2)) M) k) (Matrix.conjTranspose.{u4, u3, u1} (m' k) (n' k) α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α _inst_1 _inst_2)) (Matrix.blockDiag'.{u2, u3, u1, u4} o (fun (i : o) => m' i) (fun (k : o) => n' k) α M k))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_conj_transpose Matrix.blockDiag'_conjTransposeₓ'. -/
@[simp]
theorem blockDiag'_conjTranspose {α : Type _} [AddMonoid α] [StarAddMonoid α]
    (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) : blockDiag' Mᴴ k = (blockDiag' M k)ᴴ :=
  ext fun i j => rfl
#align matrix.block_diag'_conj_transpose Matrix.blockDiag'_conjTranspose

section Zero

variable [Zero α] [Zero β]

/- warning: matrix.block_diag'_zero -> Matrix.blockDiag'_zero is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : Zero.{u4} α], Eq.{max (succ u1) (succ (max u2 u3 u4))} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (OfNat.ofNat.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) 0 (OfNat.mk.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) 0 (Zero.zero.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.hasZero.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α _inst_1))))) (OfNat.ofNat.{max u1 u2 u3 u4} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) 0 (OfNat.mk.{max u1 u2 u3 u4} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) 0 (Zero.zero.{max u1 u2 u3 u4} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (Pi.instZero.{u1, max u2 u3 u4} o (fun (k : o) => Matrix.{u2, u3, u4} (m' k) (n' k) α) (fun (i : o) => Matrix.hasZero.{u4, u2, u3} (m' i) (n' i) α _inst_1)))))
but is expected to have type
  forall {o : Type.{u4}} {m' : o -> Type.{u3}} {n' : o -> Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α], Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (forall (k : o), Matrix.{u3, u2, u1} (m' k) (n' k) α) (Matrix.blockDiag'.{u4, u3, u2, u1} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (OfNat.ofNat.{max (max (max u4 u3) u2) u1} (Matrix.{max u3 u4, max u2 u4, u1} (Sigma.{u4, u3} o (fun (i : o) => m' i)) (Sigma.{u4, u2} o (fun (i : o) => n' i)) α) 0 (Zero.toOfNat0.{max (max (max u4 u3) u2) u1} (Matrix.{max u3 u4, max u2 u4, u1} (Sigma.{u4, u3} o (fun (i : o) => m' i)) (Sigma.{u4, u2} o (fun (i : o) => n' i)) α) (Matrix.zero.{u1, max u4 u3, max u4 u2} (Sigma.{u4, u3} o (fun (i : o) => m' i)) (Sigma.{u4, u2} o (fun (i : o) => n' i)) α _inst_1)))) (OfNat.ofNat.{max (max (max u4 u3) u2) u1} (forall (k : o), Matrix.{u3, u2, u1} (m' k) (n' k) α) 0 (Zero.toOfNat0.{max (max (max u4 u3) u2) u1} (forall (k : o), Matrix.{u3, u2, u1} (m' k) (n' k) α) (Pi.instZero.{u4, max (max u3 u2) u1} o (fun (k : o) => Matrix.{u3, u2, u1} (m' k) (n' k) α) (fun (i : o) => Matrix.zero.{u1, u3, u2} (m' i) (n' i) α _inst_1))))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_zero Matrix.blockDiag'_zeroₓ'. -/
@[simp]
theorem blockDiag'_zero : blockDiag' (0 : Matrix (Σi, m' i) (Σi, n' i) α) = 0 :=
  rfl
#align matrix.block_diag'_zero Matrix.blockDiag'_zero

/- warning: matrix.block_diag'_diagonal -> Matrix.blockDiag'_diagonal is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α] [_inst_3 : DecidableEq.{succ u1} o] [_inst_4 : forall (i : o), DecidableEq.{succ u2} (m' i)] (d : (Sigma.{u1, u2} o (fun (i : o) => m' i)) -> α) (k : o), Eq.{succ (max u2 u3)} (Matrix.{u2, u2, u3} (m' k) (m' k) α) (Matrix.blockDiag'.{u1, u2, u2, u3} o (fun (i : o) => m' i) (fun (i : o) => m' i) α (Matrix.diagonal.{u3, max u1 u2} (Sigma.{u1, u2} o (fun (i : o) => m' i)) α (fun (a : Sigma.{u1, u2} o (fun (i : o) => m' i)) (b : Sigma.{u1, u2} o (fun (i : o) => m' i)) => Sigma.decidableEq.{u1, u2} o (fun (i : o) => m' i) (fun (a : o) (b : o) => _inst_3 a b) (fun (a : o) (a_1 : m' a) (b : m' a) => _inst_4 a a_1 b) a b) _inst_1 d) k) (Matrix.diagonal.{u3, u2} (m' k) α (fun (a : m' k) (b : m' k) => _inst_4 k a b) _inst_1 (fun (i : m' k) => d (Sigma.mk.{u1, u2} o (fun (i : o) => m' i) k i)))
but is expected to have type
  forall {o : Type.{u3}} {m' : o -> Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_3 : DecidableEq.{succ u3} o] [_inst_4 : forall (i : o), DecidableEq.{succ u2} (m' i)] (d : (Sigma.{u3, u2} o (fun (i : o) => m' i)) -> α) (k : o), Eq.{max (succ u2) (succ u1)} (Matrix.{u2, u2, u1} (m' k) (m' k) α) (Matrix.blockDiag'.{u3, u2, u2, u1} o (fun (i : o) => m' i) (fun (i : o) => m' i) α (Matrix.diagonal.{u1, max u2 u3} (Sigma.{u3, u2} o (fun (i : o) => m' i)) α (fun (a : Sigma.{u3, u2} o (fun (i : o) => m' i)) (b : Sigma.{u3, u2} o (fun (i : o) => m' i)) => Sigma.instDecidableEqSigma.{u3, u2} o (fun (i : o) => m' i) (fun (a : o) (b : o) => _inst_3 a b) (fun (a : o) => (fun (a : o) (a_1 : m' a) (b : m' a) => _inst_4 a a_1 b) a) a b) _inst_1 d) k) (Matrix.diagonal.{u1, u2} (m' k) α (fun (a : m' k) (b : m' k) => _inst_4 k a b) _inst_1 (fun (i : m' k) => d (Sigma.mk.{u3, u2} o (fun (i : o) => m' i) k i)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_diagonal Matrix.blockDiag'_diagonalₓ'. -/
@[simp]
theorem blockDiag'_diagonal [DecidableEq o] [∀ i, DecidableEq (m' i)] (d : (Σi, m' i) → α) (k : o) :
    blockDiag' (diagonal d) k = diagonal fun i => d ⟨k, i⟩ :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [block_diag'_apply, diagonal_apply_eq, diagonal_apply_eq]
    · rw [block_diag'_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt (fun h => _) hij)]
      cases h; rfl
#align matrix.block_diag'_diagonal Matrix.blockDiag'_diagonal

/- warning: matrix.block_diag'_block_diagonal' -> Matrix.blockDiag'_blockDiagonal' is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : Zero.{u4} α] [_inst_3 : DecidableEq.{succ u1} o] (M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α), Eq.{max (succ u1) (succ (max u2 u3 u4))} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 M)) M
but is expected to have type
  forall {o : Type.{u4}} {m' : o -> Type.{u3}} {n' : o -> Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_3 : DecidableEq.{succ u4} o] (M : forall (i : o), Matrix.{u3, u2, u1} (m' i) (n' i) α), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (forall (k : o), Matrix.{u3, u2, u1} (m' k) (n' k) α) (Matrix.blockDiag'.{u4, u3, u2, u1} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (Matrix.blockDiagonal'.{u4, u3, u2, u1} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 M)) M
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_block_diagonal' Matrix.blockDiag'_blockDiagonal'ₓ'. -/
@[simp]
theorem blockDiag'_blockDiagonal' [DecidableEq o] (M : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiag' (blockDiagonal' M) = M :=
  funext fun k => ext fun i j => blockDiagonal'_apply_eq M _ _ _
#align matrix.block_diag'_block_diagonal' Matrix.blockDiag'_blockDiagonal'

/- warning: matrix.block_diagonal'_injective -> Matrix.blockDiagonal'_injective is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : Zero.{u4} α] [_inst_3 : DecidableEq.{succ u1} o], Function.Injective.{max (succ u1) (succ (max u2 u3 u4)), succ (max (max u1 u2) (max u1 u3) u4)} (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_3 a b) _inst_1)
but is expected to have type
  forall {o : Type.{u4}} {m' : o -> Type.{u3}} {n' : o -> Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_3 : DecidableEq.{succ u4} o], Function.Injective.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1), max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (forall (i : o), Matrix.{u3, u2, u1} (m' i) (n' i) α) (Matrix.{max u3 u4, max u2 u4, u1} (Sigma.{u4, u3} o (fun (i : o) => m' i)) (Sigma.{u4, u2} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u4, u3, u2, u1} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_3 a b) _inst_1)
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_injective Matrix.blockDiagonal'_injectiveₓ'. -/
theorem blockDiagonal'_injective [DecidableEq o] :
    Function.Injective (blockDiagonal' : (∀ i, Matrix (m' i) (n' i) α) → Matrix _ _ α) :=
  Function.LeftInverse.injective blockDiag'_blockDiagonal'
#align matrix.block_diagonal'_injective Matrix.blockDiagonal'_injective

/- warning: matrix.block_diagonal'_inj -> Matrix.blockDiagonal'_inj is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : Zero.{u4} α] [_inst_3 : DecidableEq.{succ u1} o] {M : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α} {N : forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α}, Iff (Eq.{succ (max (max u1 u2) (max u1 u3) u4)} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 M) (Matrix.blockDiagonal'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 N)) (Eq.{max (succ u1) (succ (max u2 u3 u4))} (forall (i : o), Matrix.{u2, u3, u4} (m' i) (n' i) α) M N)
but is expected to have type
  forall {o : Type.{u4}} {m' : o -> Type.{u3}} {n' : o -> Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_3 : DecidableEq.{succ u4} o] {M : forall (i : o), Matrix.{u3, u2, u1} (m' i) (n' i) α} {N : forall (i : o), Matrix.{u3, u2, u1} (m' i) (n' i) α}, Iff (Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (Matrix.{max u3 u4, max u2 u4, u1} (Sigma.{u4, u3} o (fun (i : o) => m' i)) (Sigma.{u4, u2} o (fun (i : o) => n' i)) α) (Matrix.blockDiagonal'.{u4, u3, u2, u1} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 M) (Matrix.blockDiagonal'.{u4, u3, u2, u1} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (fun (a : o) (b : o) => _inst_3 a b) _inst_1 N)) (Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (forall (i : o), Matrix.{u3, u2, u1} (m' i) (n' i) α) M N)
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_inj Matrix.blockDiagonal'_injₓ'. -/
@[simp]
theorem blockDiagonal'_inj [DecidableEq o] {M N : ∀ i, Matrix (m' i) (n' i) α} :
    blockDiagonal' M = blockDiagonal' N ↔ M = N :=
  blockDiagonal'_injective.eq_iff
#align matrix.block_diagonal'_inj Matrix.blockDiagonal'_inj

/- warning: matrix.block_diag'_one -> Matrix.blockDiag'_one is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α] [_inst_3 : DecidableEq.{succ u1} o] [_inst_4 : forall (i : o), DecidableEq.{succ u2} (m' i)] [_inst_5 : One.{u3} α], Eq.{max (succ u1) (succ (max u2 u3))} (forall (k : o), Matrix.{u2, u2, u3} (m' k) (m' k) α) (Matrix.blockDiag'.{u1, u2, u2, u3} o (fun (i : o) => m' i) (fun (i : o) => m' i) α (OfNat.ofNat.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) 1 (OfNat.mk.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) 1 (One.one.{max (max u1 u2) u3} (Matrix.{max u1 u2, max u1 u2, u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u2} o (fun (i : o) => m' i)) α) (Matrix.hasOne.{u3, max u1 u2} (Sigma.{u1, u2} o (fun (i : o) => m' i)) α (fun (a : Sigma.{u1, u2} o (fun (i : o) => m' i)) (b : Sigma.{u1, u2} o (fun (i : o) => m' i)) => Sigma.decidableEq.{u1, u2} o (fun (i : o) => m' i) (fun (a : o) (b : o) => _inst_3 a b) (fun (a : o) (a_1 : m' a) (b : m' a) => _inst_4 a a_1 b) a b) _inst_1 _inst_5))))) (OfNat.ofNat.{max u1 u2 u3} (forall (k : o), Matrix.{u2, u2, u3} (m' k) (m' k) α) 1 (OfNat.mk.{max u1 u2 u3} (forall (k : o), Matrix.{u2, u2, u3} (m' k) (m' k) α) 1 (One.one.{max u1 u2 u3} (forall (k : o), Matrix.{u2, u2, u3} (m' k) (m' k) α) (Pi.instOne.{u1, max u2 u3} o (fun (k : o) => Matrix.{u2, u2, u3} (m' k) (m' k) α) (fun (i : o) => Matrix.hasOne.{u3, u2} (m' i) α (fun (a : m' i) (b : m' i) => _inst_4 i a b) _inst_1 _inst_5)))))
but is expected to have type
  forall {o : Type.{u3}} {m' : o -> Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_3 : DecidableEq.{succ u3} o] [_inst_4 : forall (i : o), DecidableEq.{succ u2} (m' i)] [_inst_5 : One.{u1} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (forall (k : o), Matrix.{u2, u2, u1} (m' k) (m' k) α) (Matrix.blockDiag'.{u3, u2, u2, u1} o (fun (i : o) => m' i) (fun (i : o) => m' i) α (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{max u2 u3, max u2 u3, u1} (Sigma.{u3, u2} o (fun (i : o) => m' i)) (Sigma.{u3, u2} o (fun (i : o) => m' i)) α) 1 (One.toOfNat1.{max (max u3 u2) u1} (Matrix.{max u2 u3, max u2 u3, u1} (Sigma.{u3, u2} o (fun (i : o) => m' i)) (Sigma.{u3, u2} o (fun (i : o) => m' i)) α) (Matrix.one.{u1, max u3 u2} (Sigma.{u3, u2} o (fun (i : o) => m' i)) α (fun (a : Sigma.{u3, u2} o (fun (i : o) => m' i)) (b : Sigma.{u3, u2} o (fun (i : o) => m' i)) => Sigma.instDecidableEqSigma.{u3, u2} o (fun (i : o) => m' i) (fun (a : o) (b : o) => _inst_3 a b) (fun (a : o) => (fun (a : o) (a_1 : m' a) (b : m' a) => _inst_4 a a_1 b) a) a b) _inst_1 _inst_5)))) (OfNat.ofNat.{max (max u3 u2) u1} (forall (k : o), Matrix.{u2, u2, u1} (m' k) (m' k) α) 1 (One.toOfNat1.{max (max u3 u2) u1} (forall (k : o), Matrix.{u2, u2, u1} (m' k) (m' k) α) (Pi.instOne.{u3, max u2 u1} o (fun (k : o) => Matrix.{u2, u2, u1} (m' k) (m' k) α) (fun (i : o) => Matrix.one.{u1, u2} (m' i) α (fun (a : m' i) (b : m' i) => _inst_4 i a b) _inst_1 _inst_5))))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_one Matrix.blockDiag'_oneₓ'. -/
@[simp]
theorem blockDiag'_one [DecidableEq o] [∀ i, DecidableEq (m' i)] [One α] :
    blockDiag' (1 : Matrix (Σi, m' i) (Σi, m' i) α) = 1 :=
  funext <| blockDiag'_diagonal _
#align matrix.block_diag'_one Matrix.blockDiag'_one

end Zero

/- warning: matrix.block_diag'_add -> Matrix.blockDiag'_add is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : AddZeroClass.{u4} α] (M : Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (N : Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α), Eq.{max (succ u1) (succ (max u2 u3 u4))} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (HAdd.hAdd.{max (max u1 u2) (max u1 u3) u4, max (max u1 u2) (max u1 u3) u4, max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (instHAdd.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.hasAdd.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α (AddZeroClass.toHasAdd.{u4} α _inst_1))) M N)) (HAdd.hAdd.{max u1 u2 u3 u4, max u1 u2 u3 u4, max u1 u2 u3 u4} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (instHAdd.{max u1 u2 u3 u4} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (Pi.instAdd.{u1, max u2 u3 u4} o (fun (k : o) => Matrix.{u2, u3, u4} (m' k) (n' k) α) (fun (i : o) => Matrix.hasAdd.{u4, u2, u3} (m' i) (n' i) α (AddZeroClass.toHasAdd.{u4} α _inst_1)))) (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α M) (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α N))
but is expected to have type
  forall {o : Type.{u2}} {m' : o -> Type.{u3}} {n' : o -> Type.{u1}} {α : Type.{u4}} [_inst_1 : AddZeroClass.{u4} α] (M : Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (N : Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α), Eq.{max (max (max (succ u2) (succ u3)) (succ u1)) (succ u4)} (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (Matrix.blockDiag'.{u2, u3, u1, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (HAdd.hAdd.{max (max (max u2 u3) u1) u4, max (max (max u2 u3) u1) u4, max (max (max u2 u3) u1) u4} (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (instHAdd.{max (max (max u2 u3) u1) u4} (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (Matrix.add.{u4, max u2 u3, max u2 u1} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α (AddZeroClass.toAdd.{u4} α _inst_1))) M N)) (HAdd.hAdd.{max (max (max u2 u3) u1) u4, max (max (max u2 u3) u1) u4, max (max (max u2 u3) u1) u4} (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (instHAdd.{max (max (max u2 u3) u1) u4} (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (Pi.instAdd.{u2, max (max u3 u1) u4} o (fun (k : o) => Matrix.{u3, u1, u4} (m' k) (n' k) α) (fun (i : o) => Matrix.add.{u4, u3, u1} (m' i) (n' i) α (AddZeroClass.toAdd.{u4} α _inst_1)))) (Matrix.blockDiag'.{u2, u3, u1, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α M) (Matrix.blockDiag'.{u2, u3, u1, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α N))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_add Matrix.blockDiag'_addₓ'. -/
@[simp]
theorem blockDiag'_add [AddZeroClass α] (M N : Matrix (Σi, m' i) (Σi, n' i) α) :
    blockDiag' (M + N) = blockDiag' M + blockDiag' N :=
  rfl
#align matrix.block_diag'_add Matrix.blockDiag'_add

section

variable (m' n' α)

#print Matrix.blockDiag'AddMonoidHom /-
/-- `matrix.block_diag'` as an `add_monoid_hom`. -/
@[simps]
def blockDiag'AddMonoidHom [AddZeroClass α] :
    Matrix (Σi, m' i) (Σi, n' i) α →+ ∀ i, Matrix (m' i) (n' i) α
    where
  toFun := blockDiag'
  map_zero' := blockDiag'_zero
  map_add' := blockDiag'_add
#align matrix.block_diag'_add_monoid_hom Matrix.blockDiag'AddMonoidHom
-/

end

/- warning: matrix.block_diag'_neg -> Matrix.blockDiag'_neg is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : AddGroup.{u4} α] (M : Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α), Eq.{max (succ u1) (succ (max u2 u3 u4))} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (Neg.neg.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.hasNeg.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α (SubNegMonoid.toHasNeg.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1))) M)) (Neg.neg.{max u1 u2 u3 u4} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (Pi.instNeg.{u1, max u2 u3 u4} o (fun (k : o) => Matrix.{u2, u3, u4} (m' k) (n' k) α) (fun (i : o) => Matrix.hasNeg.{u4, u2, u3} (m' i) (n' i) α (SubNegMonoid.toHasNeg.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1)))) (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α M))
but is expected to have type
  forall {o : Type.{u2}} {m' : o -> Type.{u3}} {n' : o -> Type.{u1}} {α : Type.{u4}} [_inst_1 : AddGroup.{u4} α] (M : Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α), Eq.{max (max (max (succ u2) (succ u3)) (succ u1)) (succ u4)} (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (Matrix.blockDiag'.{u2, u3, u1, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (Neg.neg.{max (max (max u2 u3) u1) u4} (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (Matrix.neg.{u4, max u2 u3, max u2 u1} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_1))))) M)) (Neg.neg.{max (max (max u2 u3) u1) u4} (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (Pi.instNeg.{u2, max (max u3 u1) u4} o (fun (k : o) => Matrix.{u3, u1, u4} (m' k) (n' k) α) (fun (i : o) => Matrix.neg.{u4, u3, u1} (m' i) (n' i) α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (AddGroup.toSubtractionMonoid.{u4} α _inst_1)))))) (Matrix.blockDiag'.{u2, u3, u1, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α M))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_neg Matrix.blockDiag'_negₓ'. -/
@[simp]
theorem blockDiag'_neg [AddGroup α] (M : Matrix (Σi, m' i) (Σi, n' i) α) :
    blockDiag' (-M) = -blockDiag' M :=
  map_neg (blockDiag'AddMonoidHom m' n' α) M
#align matrix.block_diag'_neg Matrix.blockDiag'_neg

/- warning: matrix.block_diag'_sub -> Matrix.blockDiag'_sub is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} [_inst_1 : AddGroup.{u4} α] (M : Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (N : Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α), Eq.{max (succ u1) (succ (max u2 u3 u4))} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (HSub.hSub.{max (max u1 u2) (max u1 u3) u4, max (max u1 u2) (max u1 u3) u4, max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (instHSub.{max (max u1 u2) (max u1 u3) u4} (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.hasSub.{u4, max u1 u2, max u1 u3} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α (SubNegMonoid.toHasSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1)))) M N)) (HSub.hSub.{max u1 u2 u3 u4, max u1 u2 u3 u4, max u1 u2 u3 u4} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (instHSub.{max u1 u2 u3 u4} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (Pi.instSub.{u1, max u2 u3 u4} o (fun (k : o) => Matrix.{u2, u3, u4} (m' k) (n' k) α) (fun (i : o) => Matrix.hasSub.{u4, u2, u3} (m' i) (n' i) α (SubNegMonoid.toHasSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1))))) (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α M) (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α N))
but is expected to have type
  forall {o : Type.{u2}} {m' : o -> Type.{u3}} {n' : o -> Type.{u1}} {α : Type.{u4}} [_inst_1 : AddGroup.{u4} α] (M : Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (N : Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α), Eq.{max (max (max (succ u2) (succ u3)) (succ u1)) (succ u4)} (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (Matrix.blockDiag'.{u2, u3, u1, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (HSub.hSub.{max (max (max u2 u3) u1) u4, max (max (max u2 u3) u1) u4, max (max (max u2 u3) u1) u4} (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (instHSub.{max (max (max u2 u3) u1) u4} (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (Matrix.sub.{u4, max u2 u3, max u2 u1} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1)))) M N)) (HSub.hSub.{max (max (max u2 u3) u1) u4, max (max (max u2 u3) u1) u4, max (max (max u2 u3) u1) u4} (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (instHSub.{max (max (max u2 u3) u1) u4} (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (Pi.instSub.{u2, max (max u3 u1) u4} o (fun (k : o) => Matrix.{u3, u1, u4} (m' k) (n' k) α) (fun (i : o) => Matrix.sub.{u4, u3, u1} (m' i) (n' i) α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α _inst_1))))) (Matrix.blockDiag'.{u2, u3, u1, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α M) (Matrix.blockDiag'.{u2, u3, u1, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α N))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_sub Matrix.blockDiag'_subₓ'. -/
@[simp]
theorem blockDiag'_sub [AddGroup α] (M N : Matrix (Σi, m' i) (Σi, n' i) α) :
    blockDiag' (M - N) = blockDiag' M - blockDiag' N :=
  map_sub (blockDiag'AddMonoidHom m' n' α) M N
#align matrix.block_diag'_sub Matrix.blockDiag'_sub

/- warning: matrix.block_diag'_smul -> Matrix.blockDiag'_smul is a dubious translation:
lean 3 declaration is
  forall {o : Type.{u1}} {m' : o -> Type.{u2}} {n' : o -> Type.{u3}} {α : Type.{u4}} {R : Type.{u5}} [_inst_1 : Monoid.{u5} R] [_inst_2 : AddMonoid.{u4} α] [_inst_3 : DistribMulAction.{u5, u4} R α _inst_1 _inst_2] (x : R) (M : Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α), Eq.{max (succ u1) (succ (max u2 u3 u4))} (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (SMul.smul.{u5, max (max u1 u2) (max u1 u3) u4} R (Matrix.{max u1 u2, max u1 u3, u4} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) α) (Matrix.hasSmul.{u4, max u1 u2, max u1 u3, u5} (Sigma.{u1, u2} o (fun (i : o) => m' i)) (Sigma.{u1, u3} o (fun (i : o) => n' i)) R α (SMulZeroClass.toHasSmul.{u5, u4} R α (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_2)) (DistribSMul.toSmulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_2) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_1 _inst_2 _inst_3)))) x M)) (SMul.smul.{u5, max u1 u2 u3 u4} R (forall (k : o), Matrix.{u2, u3, u4} (m' k) (n' k) α) (Pi.instSMul.{u1, max u2 u3 u4, u5} o R (fun (k : o) => Matrix.{u2, u3, u4} (m' k) (n' k) α) (fun (i : o) => Matrix.hasSmul.{u4, u2, u3, u5} (m' i) (n' i) R α (SMulZeroClass.toHasSmul.{u5, u4} R α (AddZeroClass.toHasZero.{u4} α (AddMonoid.toAddZeroClass.{u4} α _inst_2)) (DistribSMul.toSmulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_2) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_1 _inst_2 _inst_3))))) x (Matrix.blockDiag'.{u1, u2, u3, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α M))
but is expected to have type
  forall {o : Type.{u2}} {m' : o -> Type.{u3}} {n' : o -> Type.{u1}} {α : Type.{u4}} {R : Type.{u5}} [_inst_1 : Monoid.{u5} R] [_inst_2 : AddMonoid.{u4} α] [_inst_3 : DistribMulAction.{u5, u4} R α _inst_1 _inst_2] (x : R) (M : Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α), Eq.{max (max (max (succ u2) (succ u3)) (succ u1)) (succ u4)} (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (Matrix.blockDiag'.{u2, u3, u1, u4} o (fun (i : o) => m' i) (fun (i : o) => n' i) α (HSMul.hSMul.{u5, max (max (max u2 u3) u1) u4, max (max (max u2 u3) u1) u4} R (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (instHSMul.{u5, max (max (max u2 u3) u1) u4} R (Matrix.{max u3 u2, max u1 u2, u4} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) α) (Matrix.smul.{u4, max u2 u3, max u2 u1, u5} (Sigma.{u2, u3} o (fun (i : o) => m' i)) (Sigma.{u2, u1} o (fun (i : o) => n' i)) R α (SMulZeroClass.toSMul.{u5, u4} R α (AddMonoid.toZero.{u4} α _inst_2) (DistribSMul.toSMulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_2) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_1 _inst_2 _inst_3))))) x M)) (HSMul.hSMul.{u5, max (max (max u4 u1) u3) u2, max (max (max u2 u3) u1) u4} R (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (instHSMul.{u5, max (max (max u2 u3) u1) u4} R (forall (k : o), Matrix.{u3, u1, u4} (m' k) (n' k) α) (Pi.instSMul.{u2, max (max u3 u1) u4, u5} o R (fun (k : o) => Matrix.{u3, u1, u4} (m' k) (n' k) α) (fun (i : o) => Matrix.smul.{u4, u3, u1, u5} (m' i) (n' i) R α (SMulZeroClass.toSMul.{u5, u4} R α (AddMonoid.toZero.{u4} α _inst_2) (DistribSMul.toSMulZeroClass.{u5, u4} R α (AddMonoid.toAddZeroClass.{u4} α _inst_2) (DistribMulAction.toDistribSMul.{u5, u4} R α _inst_1 _inst_2 _inst_3)))))) x (Matrix.blockDiag'.{u2, u3, u1, u4} o (fun (k : o) => m' k) (fun (k : o) => n' k) α M))
Case conversion may be inaccurate. Consider using '#align matrix.block_diag'_smul Matrix.blockDiag'_smulₓ'. -/
@[simp]
theorem blockDiag'_smul {R : Type _} [Monoid R] [AddMonoid α] [DistribMulAction R α] (x : R)
    (M : Matrix (Σi, m' i) (Σi, n' i) α) : blockDiag' (x • M) = x • blockDiag' M :=
  rfl
#align matrix.block_diag'_smul Matrix.blockDiag'_smul

end BlockDiag'

section

variable [CommRing R]

/- warning: matrix.to_block_mul_eq_mul -> Matrix.toBlock_mul_eq_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {m : Type.{u2}} {n : Type.{u3}} {k : Type.{u4}} [_inst_2 : Fintype.{u3} n] (p : m -> Prop) (q : k -> Prop) (A : Matrix.{u2, u3, u1} m n R) (B : Matrix.{u3, u4, u1} n k R), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u4} k (fun (a : k) => q a)) R) (Matrix.toBlock.{u2, u4, u1} m k R (Matrix.mul.{u1, u2, u3, u4} m n k R _inst_2 (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) A B) p q) (Matrix.mul.{u1, u2, u3, u4} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u3} n (fun (a : n) => Top.top.{u3} (n -> Prop) (Pi.hasTop.{u3, 0} n (fun (ᾰ : n) => Prop) (fun (i : n) => CompleteLattice.toHasTop.{0} Prop Prop.completeLattice)) a)) (Subtype.{succ u4} k (fun (a : k) => q a)) R (Subtype.fintype.{u3} n (fun (a : n) => Top.top.{u3} (n -> Prop) (Pi.hasTop.{u3, 0} n (fun (ᾰ : n) => Prop) (fun (i : n) => CompleteLattice.toHasTop.{0} Prop Prop.completeLattice)) a) (fun (a : n) => decidableTrue) _inst_2) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.toBlock.{u2, u3, u1} m n R A p (Top.top.{u3} (n -> Prop) (Pi.hasTop.{u3, 0} n (fun (ᾰ : n) => Prop) (fun (i : n) => CompleteLattice.toHasTop.{0} Prop Prop.completeLattice)))) (Matrix.toBlock.{u3, u4, u1} n k R B (Top.top.{u3} (n -> Prop) (Pi.hasTop.{u3, 0} n (fun (ᾰ : n) => Prop) (fun (i : n) => CompleteLattice.toHasTop.{0} Prop Prop.completeLattice))) q))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {m : Type.{u4}} {n : Type.{u3}} {k : Type.{u2}} [_inst_2 : Fintype.{u3} n] (p : m -> Prop) (q : k -> Prop) (A : Matrix.{u4, u3, u1} m n R) (B : Matrix.{u3, u2, u1} n k R), Eq.{max (max (succ u1) (succ u4)) (succ u2)} (Matrix.{u4, u2, u1} (Subtype.{succ u4} m (fun (a : m) => p a)) (Subtype.{succ u2} k (fun (a : k) => q a)) R) (Matrix.toBlock.{u4, u2, u1} m k R (Matrix.mul.{u1, u4, u3, u2} m n k R _inst_2 (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) A B) p q) (Matrix.mul.{u1, u4, u3, u2} (Subtype.{succ u4} m (fun (a : m) => p a)) (Subtype.{succ u3} n (fun (a : n) => Top.top.{u3} (n -> Prop) (Pi.instTopForAll.{u3, 0} n (fun (ᾰ : n) => Prop) (fun (i : n) => CompleteLattice.toTop.{0} Prop Prop.completeLattice)) a)) (Subtype.{succ u2} k (fun (a : k) => q a)) R (Subtype.fintype.{u3} n (fun (a : n) => Top.top.{u3} (n -> Prop) (Pi.instTopForAll.{u3, 0} n (fun (ᾰ : n) => Prop) (fun (i : n) => CompleteLattice.toTop.{0} Prop Prop.completeLattice)) a) (fun (a : n) => Prop.decidablePredTop.{u3} n a) _inst_2) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.toBlock.{u4, u3, u1} m n R A p (Top.top.{u3} (n -> Prop) (Pi.instTopForAll.{u3, 0} n (fun (ᾰ : n) => Prop) (fun (i : n) => CompleteLattice.toTop.{0} Prop Prop.completeLattice)))) (Matrix.toBlock.{u3, u2, u1} n k R B (Top.top.{u3} (n -> Prop) (Pi.instTopForAll.{u3, 0} n (fun (ᾰ : n) => Prop) (fun (i : n) => CompleteLattice.toTop.{0} Prop Prop.completeLattice))) q))
Case conversion may be inaccurate. Consider using '#align matrix.to_block_mul_eq_mul Matrix.toBlock_mul_eq_mulₓ'. -/
theorem toBlock_mul_eq_mul {m n k : Type _} [Fintype n] (p : m → Prop) (q : k → Prop)
    (A : Matrix m n R) (B : Matrix n k R) : (A ⬝ B).toBlock p q = A.toBlock p ⊤ ⬝ B.toBlock ⊤ q :=
  by
  ext (i k)
  simp only [to_block_apply, mul_apply]
  rw [Finset.sum_subtype]
  simp [Top.top, CompleteLattice.top, BoundedOrder.top]
#align matrix.to_block_mul_eq_mul Matrix.toBlock_mul_eq_mul

/- warning: matrix.to_block_mul_eq_add -> Matrix.toBlock_mul_eq_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {m : Type.{u2}} {n : Type.{u3}} {k : Type.{u4}} [_inst_2 : Fintype.{u3} n] (p : m -> Prop) (q : n -> Prop) [_inst_3 : DecidablePred.{succ u3} n q] (r : k -> Prop) (A : Matrix.{u2, u3, u1} m n R) (B : Matrix.{u3, u4, u1} n k R), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u4} k (fun (a : k) => r a)) R) (Matrix.toBlock.{u2, u4, u1} m k R (Matrix.mul.{u1, u2, u3, u4} m n k R _inst_2 (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) A B) p r) (HAdd.hAdd.{max u2 u4 u1, max u2 u4 u1, max u2 u4 u1} (Matrix.{u2, u4, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u4} k (fun (a : k) => r a)) R) (Matrix.{u2, u4, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u4} k (fun (a : k) => r a)) R) (Matrix.{u2, u4, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u4} k (fun (a : k) => r a)) R) (instHAdd.{max u2 u4 u1} (Matrix.{u2, u4, u1} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u4} k (fun (a : k) => r a)) R) (Matrix.hasAdd.{u1, u2, u4} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u4} k (fun (a : k) => r a)) R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.mul.{u1, u2, u3, u4} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u3} n (fun (a : n) => q a)) (Subtype.{succ u4} k (fun (a : k) => r a)) R (Subtype.fintype.{u3} n (fun (a : n) => q a) (fun (a : n) => _inst_3 a) _inst_2) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.toBlock.{u2, u3, u1} m n R A p q) (Matrix.toBlock.{u3, u4, u1} n k R B q r)) (Matrix.mul.{u1, u2, u3, u4} (Subtype.{succ u2} m (fun (a : m) => p a)) (Subtype.{succ u3} n (fun (a : n) => Not (q a))) (Subtype.{succ u4} k (fun (a : k) => r a)) R (Subtype.fintype.{u3} n (fun (a : n) => Not (q a)) (fun (a : n) => Not.decidable (q a) (_inst_3 a)) _inst_2) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.toBlock.{u2, u3, u1} m n R A p (fun (i : n) => Not (q i))) (Matrix.toBlock.{u3, u4, u1} n k R B (fun (i : n) => Not (q i)) r)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {m : Type.{u4}} {n : Type.{u3}} {k : Type.{u2}} [_inst_2 : Fintype.{u3} n] (p : m -> Prop) (q : n -> Prop) [_inst_3 : DecidablePred.{succ u3} n q] (r : k -> Prop) (A : Matrix.{u4, u3, u1} m n R) (B : Matrix.{u3, u2, u1} n k R), Eq.{max (max (succ u1) (succ u4)) (succ u2)} (Matrix.{u4, u2, u1} (Subtype.{succ u4} m (fun (a : m) => p a)) (Subtype.{succ u2} k (fun (a : k) => r a)) R) (Matrix.toBlock.{u4, u2, u1} m k R (Matrix.mul.{u1, u4, u3, u2} m n k R _inst_2 (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) A B) p r) (HAdd.hAdd.{max (max u1 u4) u2, max (max u1 u4) u2, max (max u1 u4) u2} (Matrix.{u4, u2, u1} (Subtype.{succ u4} m (fun (a : m) => p a)) (Subtype.{succ u2} k (fun (a : k) => r a)) R) (Matrix.{u4, u2, u1} (Subtype.{succ u4} m (fun (a : m) => p a)) (Subtype.{succ u2} k (fun (a : k) => r a)) R) (Matrix.{u4, u2, u1} (Subtype.{succ u4} m (fun (a : m) => p a)) (Subtype.{succ u2} k (fun (a : k) => r a)) R) (instHAdd.{max (max u1 u4) u2} (Matrix.{u4, u2, u1} (Subtype.{succ u4} m (fun (a : m) => p a)) (Subtype.{succ u2} k (fun (a : k) => r a)) R) (Matrix.add.{u1, u4, u2} (Subtype.{succ u4} m (fun (a : m) => p a)) (Subtype.{succ u2} k (fun (a : k) => r a)) R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) (Matrix.mul.{u1, u4, u3, u2} (Subtype.{succ u4} m (fun (a : m) => p a)) (Subtype.{succ u3} n (fun (a : n) => q a)) (Subtype.{succ u2} k (fun (a : k) => r a)) R (Subtype.fintype.{u3} n (fun (a : n) => q a) (fun (a : n) => _inst_3 a) _inst_2) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.toBlock.{u4, u3, u1} m n R A p q) (Matrix.toBlock.{u3, u2, u1} n k R B q r)) (Matrix.mul.{u1, u4, u3, u2} (Subtype.{succ u4} m (fun (a : m) => p a)) (Subtype.{succ u3} n (fun (a : n) => Not (q a))) (Subtype.{succ u2} k (fun (a : k) => r a)) R (Subtype.fintype.{u3} n (fun (a : n) => Not (q a)) (fun (a : n) => instDecidableNot (q a) (_inst_3 a)) _inst_2) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.toBlock.{u4, u3, u1} m n R A p (fun (i : n) => Not (q i))) (Matrix.toBlock.{u3, u2, u1} n k R B (fun (i : n) => Not (q i)) r)))
Case conversion may be inaccurate. Consider using '#align matrix.to_block_mul_eq_add Matrix.toBlock_mul_eq_addₓ'. -/
theorem toBlock_mul_eq_add {m n k : Type _} [Fintype n] (p : m → Prop) (q : n → Prop)
    [DecidablePred q] (r : k → Prop) (A : Matrix m n R) (B : Matrix n k R) :
    (A ⬝ B).toBlock p r =
      A.toBlock p q ⬝ B.toBlock q r + (A.toBlock p fun i => ¬q i) ⬝ B.toBlock (fun i => ¬q i) r :=
  by
  classical
    ext (i k)
    simp only [to_block_apply, mul_apply, Pi.add_apply]
    convert(Fintype.sum_subtype_add_sum_subtype q fun x => A (↑i) x * B x ↑k).symm
#align matrix.to_block_mul_eq_add Matrix.toBlock_mul_eq_add

end

end Matrix

