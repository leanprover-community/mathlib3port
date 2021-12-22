import Mathbin.Data.Matrix.Basic
import Mathbin.Data.Fin.VecNotation

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

open_locale Matrix

/--  Use `![...]` notation for displaying a `fin`-indexed matrix, for example:

```
#eval ![![1, 2], ![3, 4]] + ![![3, 4], ![5, 6]] -- ![![4, 6], ![8, 10]]
```
-/
instance [HasRepr α] : HasRepr (Matrix (Finₓ m) (Finₓ n) α) :=
  pi_fin.has_repr

@[simp]
theorem cons_val' (v : n' → α) (B : Matrix (Finₓ m) n' α) i j : vec_cons v B i j = vec_cons (v j) (fun i => B i j) i :=
  by
  refine' Finₓ.cases _ _ i <;> simp

@[simp]
theorem head_val' (B : Matrix (Finₓ m.succ) n' α) (j : n') : (vec_head fun i => B i j) = vec_head B j :=
  rfl

@[simp]
theorem tail_val' (B : Matrix (Finₓ m.succ) n' α) (j : n') : (vec_tail fun i => B i j) = fun i => vec_tail B i j := by
  ext
  simp [vec_tail]

section DotProduct

variable [AddCommMonoidₓ α] [Mul α]

@[simp]
theorem dot_product_empty (v w : Finₓ 0 → α) : dot_product v w = 0 :=
  Finset.sum_empty

@[simp]
theorem cons_dot_product (x : α) (v : Finₓ n → α) (w : Finₓ n.succ → α) :
    dot_product (vec_cons x v) w = (x*vec_head w)+dot_product v (vec_tail w) := by
  simp [dot_product, Finₓ.sum_univ_succ, vec_head, vec_tail]

@[simp]
theorem dot_product_cons (v : Finₓ n.succ → α) (x : α) (w : Finₓ n → α) :
    dot_product v (vec_cons x w) = (vec_head v*x)+dot_product (vec_tail v) w := by
  simp [dot_product, Finₓ.sum_univ_succ, vec_head, vec_tail]

end DotProduct

section ColRow

@[simp]
theorem col_empty (v : Finₓ 0 → α) : col v = vec_empty :=
  empty_eq _

@[simp]
theorem col_cons (x : α) (u : Finₓ m → α) : col (vec_cons x u) = vec_cons (fun _ => x) (col u) := by
  ext i j
  refine' Finₓ.cases _ _ i <;> simp [vec_head, vec_tail]

@[simp]
theorem row_empty : row (vec_empty : Finₓ 0 → α) = fun _ => vec_empty := by
  ext
  rfl

@[simp]
theorem row_cons (x : α) (u : Finₓ m → α) : row (vec_cons x u) = fun _ => vec_cons x u := by
  ext
  rfl

end ColRow

section Transpose

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»
@[simp]
theorem transpose_empty_rows (A : Matrix m' (Finₓ 0) α) :
    (A)ᵀ = «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»" :=
  empty_eq _

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»
@[simp]
theorem transpose_empty_cols :
    ((«expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»" :
          Matrix (Finₓ 0) m' α))ᵀ =
      fun i => «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»" :=
  funext fun i => empty_eq _

@[simp]
theorem cons_transpose (v : n' → α) (A : Matrix (Finₓ m) n' α) : (vec_cons v A)ᵀ = fun i => vec_cons (v i) ((A)ᵀ i) :=
  by
  ext i j
  refine' Finₓ.cases _ _ j <;> simp

@[simp]
theorem head_transpose (A : Matrix m' (Finₓ n.succ) α) : vec_head (A)ᵀ = vec_head ∘ A :=
  rfl

@[simp]
theorem tail_transpose (A : Matrix m' (Finₓ n.succ) α) : vec_tail (A)ᵀ = (vec_tail ∘ A)ᵀ := by
  ext i j
  rfl

end Transpose

section Mul

variable [Semiringₓ α]

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»
@[simp]
theorem empty_mul [Fintype n'] (A : Matrix (Finₓ 0) n' α) (B : Matrix n' o' α) :
    A ⬝ B = «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»" :=
  empty_eq _

@[simp]
theorem empty_mul_empty (A : Matrix m' (Finₓ 0) α) (B : Matrix (Finₓ 0) o' α) : A ⬝ B = 0 :=
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»
@[simp]
theorem mul_empty [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Finₓ 0) α) :
    A ⬝ B = fun _ =>
      «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»" :=
  funext fun _ => empty_eq _

theorem mul_val_succ [Fintype n'] (A : Matrix (Finₓ m.succ) n' α) (B : Matrix n' o' α) (i : Finₓ m) (j : o') :
    (A ⬝ B) i.succ j = (vec_tail A ⬝ B) i j :=
  rfl

@[simp]
theorem cons_mul [Fintype n'] (v : n' → α) (A : Matrix (Finₓ m) n' α) (B : Matrix n' o' α) :
    vec_cons v A ⬝ B = vec_cons (vec_mul v B) (A ⬝ B) := by
  ext i j
  refine' Finₓ.cases _ _ i
  ·
    rfl
  simp [mul_val_succ]

end Mul

section VecMul

variable [Semiringₓ α]

@[simp]
theorem empty_vec_mul (v : Finₓ 0 → α) (B : Matrix (Finₓ 0) o' α) : vec_mul v B = 0 :=
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»
@[simp]
theorem vec_mul_empty [Fintype n'] (v : n' → α) (B : Matrix n' (Finₓ 0) α) :
    vec_mul v B = «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»" :=
  empty_eq _

@[simp]
theorem cons_vec_mul (x : α) (v : Finₓ n → α) (B : Matrix (Finₓ n.succ) o' α) :
    vec_mul (vec_cons x v) B = (x • vec_head B)+vec_mul v (vec_tail B) := by
  ext i
  simp [vec_mul]

@[simp]
theorem vec_mul_cons (v : Finₓ n.succ → α) (w : o' → α) (B : Matrix (Finₓ n) o' α) :
    vec_mul v (vec_cons w B) = (vec_head v • w)+vec_mul (vec_tail v) B := by
  ext i
  simp [vec_mul]

end VecMul

section MulVec

variable [Semiringₓ α]

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»
@[simp]
theorem empty_mul_vec [Fintype n'] (A : Matrix (Finₓ 0) n' α) (v : n' → α) :
    mul_vec A v = «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»" :=
  empty_eq _

@[simp]
theorem mul_vec_empty (A : Matrix m' (Finₓ 0) α) (v : Finₓ 0 → α) : mul_vec A v = 0 :=
  rfl

@[simp]
theorem cons_mul_vec [Fintype n'] (v : n' → α) (A : Finₓ m → n' → α) (w : n' → α) :
    mul_vec (vec_cons v A) w = vec_cons (dot_product v w) (mul_vec A w) := by
  ext i
  refine' Finₓ.cases _ _ i <;> simp [mul_vec]

@[simp]
theorem mul_vec_cons {α} [CommSemiringₓ α] (A : m' → Finₓ n.succ → α) (x : α) (v : Finₓ n → α) :
    mul_vec A (vec_cons x v) = (x • vec_head ∘ A)+mul_vec (vec_tail ∘ A) v := by
  ext i
  simp [mul_vec, mul_commₓ]

end MulVec

section VecMulVec

variable [Semiringₓ α]

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»
@[simp]
theorem empty_vec_mul_vec (v : Finₓ 0 → α) (w : n' → α) :
    vec_mul_vec v w =
      «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»" :=
  empty_eq _

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»
@[simp]
theorem vec_mul_vec_empty (v : m' → α) (w : Finₓ 0 → α) :
    vec_mul_vec v w = fun _ =>
      «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»" :=
  funext fun i => empty_eq _

@[simp]
theorem cons_vec_mul_vec (x : α) (v : Finₓ m → α) (w : n' → α) :
    vec_mul_vec (vec_cons x v) w = vec_cons (x • w) (vec_mul_vec v w) := by
  ext i
  refine' Finₓ.cases _ _ i <;> simp [vec_mul_vec]

@[simp]
theorem vec_mul_vec_cons (v : m' → α) (x : α) (w : Finₓ n → α) :
    vec_mul_vec v (vec_cons x w) = fun i => v i • vec_cons x w := by
  ext i j
  rw [vec_mul_vec, Pi.smul_apply, smul_eq_mul]

end VecMulVec

section Smul

variable [Semiringₓ α]

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»
@[simp]
theorem smul_mat_empty {m' : Type _} (x : α) (A : Finₓ 0 → m' → α) :
    x • A = «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»" :=
  empty_eq _

@[simp]
theorem smul_mat_cons (x : α) (v : n' → α) (A : Matrix (Finₓ m) n' α) : x • vec_cons v A = vec_cons (x • v) (x • A) :=
  by
  ext i
  refine' Finₓ.cases _ _ i <;> simp

end Smul

section Minor

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»
@[simp]
theorem minor_empty (A : Matrix m' n' α) (row : Finₓ 0 → m') (col : o' → n') :
    minor A row col =
      «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr![ , ]»" :=
  empty_eq _

@[simp]
theorem minor_cons_row (A : Matrix m' n' α) (i : m') (row : Finₓ m → m') (col : o' → n') :
    minor A (vec_cons i row) col = vec_cons (fun j => A i (col j)) (minor A row col) := by
  ext i j
  refine' Finₓ.cases _ _ i <;> simp [minor]

end Minor

end Matrix

