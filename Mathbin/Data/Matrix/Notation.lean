/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.Data.Fin.VecNotation
import Mathbin.Tactic.FinCases
import Mathbin.Algebra.BigOperators.Fin

/-!
# Matrix and vector notation

This file includes `simp` lemmas for applying operations in `data.matrix.basic` to values built out
of the matrix notation `![a, b] = vec_cons a (vec_cons b vec_empty)` defined in
`data.fin.vec_notation`.

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vec_cons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

We reuse notation `![a, b]` for `vec_cons a (vec_cons b vec_empty)`. It is a localized notation in
the `matrix` locale.

## Examples

Examples of usage can be found in the `test/matrix.lean` file.
-/


namespace Matrix

universe u

variable {α : Type u} {o n m : ℕ} {m' n' o' : Type _}

open Matrix

/-- Use `![...]` notation for displaying a `fin`-indexed matrix, for example:

```
#eval ![![1, 2], ![3, 4]] + ![![3, 4], ![5, 6]] -- ![![4, 6], ![8, 10]]
```
-/
instance [HasRepr α] : HasRepr (Matrix (Finₓ m) (Finₓ n) α) :=
  pi_fin.has_repr

@[simp]
theorem cons_val' (v : n' → α) (B : Matrix (Finₓ m) n' α) i j : vecCons v B i j = vecCons (v j) (fun i => B i j) i := by
  refine' Finₓ.cases _ _ i <;> simp

@[simp]
theorem head_val' (B : Matrix (Finₓ m.succ) n' α) (j : n') : (vecHead fun i => B i j) = vecHead B j :=
  rfl

@[simp]
theorem tail_val' (B : Matrix (Finₓ m.succ) n' α) (j : n') : (vecTail fun i => B i j) = fun i => vecTail B i j := by
  ext
  simp [vec_tail]

section DotProduct

variable [AddCommMonoidₓ α] [Mul α]

@[simp]
theorem dot_product_empty (v w : Finₓ 0 → α) : dotProduct v w = 0 :=
  Finset.sum_empty

@[simp]
theorem cons_dot_product (x : α) (v : Finₓ n → α) (w : Finₓ n.succ → α) :
    dotProduct (vecCons x v) w = x * vecHead w + dotProduct v (vecTail w) := by
  simp [dot_product, Finₓ.sum_univ_succ, vec_head, vec_tail]

@[simp]
theorem dot_product_cons (v : Finₓ n.succ → α) (x : α) (w : Finₓ n → α) :
    dotProduct v (vecCons x w) = vecHead v * x + dotProduct (vecTail v) w := by
  simp [dot_product, Finₓ.sum_univ_succ, vec_head, vec_tail]

@[simp]
theorem cons_dot_product_cons (x : α) (v : Finₓ n → α) (y : α) (w : Finₓ n → α) :
    dotProduct (vecCons x v) (vecCons y w) = x * y + dotProduct v w := by
  simp

end DotProduct

section ColRow

@[simp]
theorem col_empty (v : Finₓ 0 → α) : colₓ v = vec_empty :=
  empty_eq _

@[simp]
theorem col_cons (x : α) (u : Finₓ m → α) : colₓ (vecCons x u) = vecCons (fun _ => x) (colₓ u) := by
  ext i j
  refine' Finₓ.cases _ _ i <;> simp [vec_head, vec_tail]

@[simp]
theorem row_empty : rowₓ (vecEmpty : Finₓ 0 → α) = fun _ => vecEmpty := by
  ext
  rfl

@[simp]
theorem row_cons (x : α) (u : Finₓ m → α) : rowₓ (vecCons x u) = fun _ => vecCons x u := by
  ext
  rfl

end ColRow

section Transpose

@[simp]
theorem transpose_empty_rows (A : Matrix m' (Finₓ 0) α) : Aᵀ = ![] :=
  empty_eq _

@[simp]
theorem transpose_empty_cols : (![] : Matrix (Finₓ 0) m' α)ᵀ = fun i => ![] :=
  funext fun i => empty_eq _

@[simp]
theorem cons_transpose (v : n' → α) (A : Matrix (Finₓ m) n' α) : (vecCons v A)ᵀ = fun i => vecCons (v i) (Aᵀ i) := by
  ext i j
  refine' Finₓ.cases _ _ j <;> simp

@[simp]
theorem head_transpose (A : Matrix m' (Finₓ n.succ) α) : vecHead Aᵀ = vec_head ∘ A :=
  rfl

@[simp]
theorem tail_transpose (A : Matrix m' (Finₓ n.succ) α) : vecTail Aᵀ = (vec_tail ∘ A)ᵀ := by
  ext i j
  rfl

end Transpose

section Mul

variable [Semiringₓ α]

@[simp]
theorem empty_mul [Fintype n'] (A : Matrix (Finₓ 0) n' α) (B : Matrix n' o' α) : A ⬝ B = ![] :=
  empty_eq _

@[simp]
theorem empty_mul_empty (A : Matrix m' (Finₓ 0) α) (B : Matrix (Finₓ 0) o' α) : A ⬝ B = 0 :=
  rfl

@[simp]
theorem mul_empty [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Finₓ 0) α) : A ⬝ B = fun _ => ![] :=
  funext fun _ => empty_eq _

theorem mul_val_succ [Fintype n'] (A : Matrix (Finₓ m.succ) n' α) (B : Matrix n' o' α) (i : Finₓ m) (j : o') :
    (A ⬝ B) i.succ j = (vecTail A ⬝ B) i j :=
  rfl

@[simp]
theorem cons_mul [Fintype n'] (v : n' → α) (A : Matrix (Finₓ m) n' α) (B : Matrix n' o' α) :
    vecCons v A ⬝ B = vecCons (vecMulₓ v B) (A ⬝ B) := by
  ext i j
  refine' Finₓ.cases _ _ i
  · rfl
    
  simp [mul_val_succ]

end Mul

section VecMul

variable [Semiringₓ α]

@[simp]
theorem empty_vec_mul (v : Finₓ 0 → α) (B : Matrix (Finₓ 0) o' α) : vecMulₓ v B = 0 :=
  rfl

@[simp]
theorem vec_mul_empty [Fintype n'] (v : n' → α) (B : Matrix n' (Finₓ 0) α) : vecMulₓ v B = ![] :=
  empty_eq _

@[simp]
theorem cons_vec_mul (x : α) (v : Finₓ n → α) (B : Matrix (Finₓ n.succ) o' α) :
    vecMulₓ (vecCons x v) B = x • vecHead B + vecMulₓ v (vecTail B) := by
  ext i
  simp [vec_mul]

@[simp]
theorem vec_mul_cons (v : Finₓ n.succ → α) (w : o' → α) (B : Matrix (Finₓ n) o' α) :
    vecMulₓ v (vecCons w B) = vecHead v • w + vecMulₓ (vecTail v) B := by
  ext i
  simp [vec_mul]

end VecMul

section MulVec

variable [Semiringₓ α]

@[simp]
theorem empty_mul_vec [Fintype n'] (A : Matrix (Finₓ 0) n' α) (v : n' → α) : mulVecₓ A v = ![] :=
  empty_eq _

@[simp]
theorem mul_vec_empty (A : Matrix m' (Finₓ 0) α) (v : Finₓ 0 → α) : mulVecₓ A v = 0 :=
  rfl

@[simp]
theorem cons_mul_vec [Fintype n'] (v : n' → α) (A : Finₓ m → n' → α) (w : n' → α) :
    mulVecₓ (vecCons v A) w = vecCons (dotProduct v w) (mulVecₓ A w) := by
  ext i
  refine' Finₓ.cases _ _ i <;> simp [mul_vec]

@[simp]
theorem mul_vec_cons {α} [CommSemiringₓ α] (A : m' → Finₓ n.succ → α) (x : α) (v : Finₓ n → α) :
    mulVecₓ A (vecCons x v) = x • vec_head ∘ A + mulVecₓ (vec_tail ∘ A) v := by
  ext i
  simp [mul_vec, mul_comm]

end MulVec

section VecMulVec

variable [Semiringₓ α]

@[simp]
theorem empty_vec_mul_vec (v : Finₓ 0 → α) (w : n' → α) : vecMulVecₓ v w = ![] :=
  empty_eq _

@[simp]
theorem vec_mul_vec_empty (v : m' → α) (w : Finₓ 0 → α) : vecMulVecₓ v w = fun _ => ![] :=
  funext fun i => empty_eq _

@[simp]
theorem cons_vec_mul_vec (x : α) (v : Finₓ m → α) (w : n' → α) :
    vecMulVecₓ (vecCons x v) w = vecCons (x • w) (vecMulVecₓ v w) := by
  ext i
  refine' Finₓ.cases _ _ i <;> simp [vec_mul_vec]

@[simp]
theorem vec_mul_vec_cons (v : m' → α) (x : α) (w : Finₓ n → α) :
    vecMulVecₓ v (vecCons x w) = fun i => v i • vecCons x w := by
  ext i j
  rw [vec_mul_vec, Pi.smul_apply, smul_eq_mul]

end VecMulVec

section Smul

variable [Semiringₓ α]

@[simp]
theorem smul_mat_empty {m' : Type _} (x : α) (A : Finₓ 0 → m' → α) : x • A = ![] :=
  empty_eq _

@[simp]
theorem smul_mat_cons (x : α) (v : n' → α) (A : Matrix (Finₓ m) n' α) : x • vecCons v A = vecCons (x • v) (x • A) := by
  ext i
  refine' Finₓ.cases _ _ i <;> simp

end Smul

section Minor

@[simp]
theorem minor_empty (A : Matrix m' n' α) (row : Finₓ 0 → m') (col : o' → n') : minor A row col = ![] :=
  empty_eq _

@[simp]
theorem minor_cons_row (A : Matrix m' n' α) (i : m') (row : Finₓ m → m') (col : o' → n') :
    minor A (vecCons i row) col = vecCons (fun j => A i (col j)) (minor A row col) := by
  ext i j
  refine' Finₓ.cases _ _ i <;> simp [minor]

end Minor

section Vec2AndVec3

section One

variable [Zero α] [One α]

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
theorem one_fin_two : (1 : Matrix (Finₓ 2) (Finₓ 2) α) = ![![1, 0], ![0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
theorem one_fin_three : (1 : Matrix (Finₓ 3) (Finₓ 3) α) = ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end One

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
theorem mul_fin_two [AddCommMonoidₓ α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    ![![a₁₁, a₁₂], ![a₂₁, a₂₂]] ⬝ ![![b₁₁, b₁₂], ![b₂₁, b₂₂]] =
      ![![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂], ![a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂]] :=
  by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul, dot_product, Finₓ.sum_univ_succ]

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
theorem mul_fin_three [AddCommMonoidₓ α] [Mul α]
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
    ![![a₁₁, a₁₂, a₁₃], ![a₂₁, a₂₂, a₂₃], ![a₃₁, a₃₂, a₃₃]] ⬝ ![![b₁₁, b₁₂, b₁₃], ![b₂₁, b₂₂, b₂₃], ![b₃₁, b₃₂, b₃₃]] =
      ![![a₁₁ * b₁₁ + a₁₂ * b₂₁ + a₁₃ * b₃₁, a₁₁ * b₁₂ + a₁₂ * b₂₂ + a₁₃ * b₃₂, a₁₁ * b₁₃ + a₁₂ * b₂₃ + a₁₃ * b₃₃],
        ![a₂₁ * b₁₁ + a₂₂ * b₂₁ + a₂₃ * b₃₁, a₂₁ * b₁₂ + a₂₂ * b₂₂ + a₂₃ * b₃₂, a₂₁ * b₁₃ + a₂₂ * b₂₃ + a₂₃ * b₃₃],
        ![a₃₁ * b₁₁ + a₃₂ * b₂₁ + a₃₃ * b₃₁, a₃₁ * b₁₂ + a₃₂ * b₂₂ + a₃₃ * b₃₂, a₃₁ * b₁₃ + a₃₂ * b₂₃ + a₃₃ * b₃₃]] :=
  by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul, dot_product, Finₓ.sum_univ_succ, ← add_assocₓ]

theorem vec2_eq {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) : ![a₀, a₁] = ![b₀, b₁] := by
  subst_vars

theorem vec3_eq {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) : ![a₀, a₁, a₂] = ![b₀, b₁, b₂] :=
  by
  subst_vars

theorem vec2_add [Add α] (a₀ a₁ b₀ b₁ : α) : ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁] := by
  rw [cons_add_cons, cons_add_cons, empty_add_empty]

theorem vec3_add [Add α] (a₀ a₁ a₂ b₀ b₁ b₂ : α) : ![a₀, a₁, a₂] + ![b₀, b₁, b₂] = ![a₀ + b₀, a₁ + b₁, a₂ + b₂] := by
  rw [cons_add_cons, cons_add_cons, cons_add_cons, empty_add_empty]

theorem smul_vec2 {R : Type _} [HasScalar R α] (x : R) (a₀ a₁ : α) : x • ![a₀, a₁] = ![x • a₀, x • a₁] := by
  rw [smul_cons, smul_cons, smul_empty]

theorem smul_vec3 {R : Type _} [HasScalar R α] (x : R) (a₀ a₁ a₂ : α) : x • ![a₀, a₁, a₂] = ![x • a₀, x • a₁, x • a₂] :=
  by
  rw [smul_cons, smul_cons, smul_cons, smul_empty]

variable [AddCommMonoidₓ α] [Mul α]

theorem vec2_dot_product' {a₀ a₁ b₀ b₁ : α} : ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁ := by
  rw [cons_dot_product_cons, cons_dot_product_cons, dot_product_empty, add_zeroₓ]

@[simp]
theorem vec2_dot_product (v w : Finₓ 2 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 :=
  vec2_dot_product'

theorem vec3_dot_product' {a₀ a₁ a₂ b₀ b₁ b₂ : α} : ![a₀, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] = a₀ * b₀ + a₁ * b₁ + a₂ * b₂ := by
  rw [cons_dot_product_cons, cons_dot_product_cons, cons_dot_product_cons, dot_product_empty, add_zeroₓ, add_assocₓ]

@[simp]
theorem vec3_dot_product (v w : Finₓ 3 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
  vec3_dot_product'

end Vec2AndVec3

end Matrix

