/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser

! This file was ported from Lean 3 source module data.matrix.notation
! leanprover-community/mathlib commit 86d1873c01a723aba6788f0b9051ae3d23b4c1c3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.Data.Fin.VecNotation
import Mathbin.Tactic.FinCases
import Mathbin.Algebra.BigOperators.Fin

/-!
# Matrix and vector notation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file includes `simp` lemmas for applying operations in `data.matrix.basic` to values built out
of the matrix notation `![a, b] = vec_cons a (vec_cons b vec_empty)` defined in
`data.fin.vec_notation`.

This also provides the new notation `!![a, b; c, d] = matrix.of ![![a, b], ![c, d]]`.
This notation also works for empty matrices; `!![,,,] : matrix (fin 0) (fin 3)` and
`!![;;;] : matrix (fin 3) (fin 0)`.

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vec_cons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

This file provide notation `!![a, b; c, d]` for matrices, which corresponds to
`matrix.of ![![a, b], ![c, d]]`.
A parser for `a, b; c, d`-style strings is provided as `matrix.entry_parser`, while
`matrix.notation` provides the hook for the `!!` notation.
Note that in lean 3 the pretty-printer will not show `!!` notation, instead showing the version
with `of ![![...]]`.

## Examples

Examples of usage can be found in the `test/matrix.lean` file.
-/


namespace Matrix

universe u

variable {α : Type u} {o n m : ℕ} {m' n' o' : Type _}

open Matrix

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[] -/
#print Matrix.toExpr /-
/-- Matrices can be reflected whenever their entries can. We insert an `@id (matrix m' n' α)` to
prevent immediate decay to a function. -/
unsafe instance Matrix.toExpr [Lean.ToLevel.{u}] [Lean.ToLevel.{u_1}] [Lean.ToLevel.{u_2}]
    [reflected _ α] [reflected _ m'] [reflected _ n'] [h : has_reflect (m' → n' → α)] :
    has_reflect (Matrix m' n' α) := fun m =>
  (by
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[]" :
          reflected _ @id.{max u_1 u_2 u + 1}).subst₂
      ((by
            trace
              "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[]" :
            reflected _ @Matrix.{u_1, u_2, u}).subst₃
        q(_) q(_) q(_)) <|
    by
    dsimp only [Matrix]
    exact h m
#align matrix.matrix.reflect Matrix.toExpr
-/

section Parser

open Lean

open Lean.Parser

open Interactive

open Interactive.Types

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Parse the entries of a matrix -/
unsafe def entry_parser {α : Type} (p : parser α) : parser (Σm n, Fin m → Fin n → α) := do
  let-- a list of lists if the matrix has at least one row, or the number of columns if the matrix has
  -- zero rows.
  p :
    parser (Sum (List (List α)) ℕ) :=-- empty rows
        Sum.inl <$>
        ((pure [] <* tk ";").repeat_at_least 1 <|>
          (sep_by_trailing (tk ";") <| sep_by_trailing (tk ",") p)) <|>
      Sum.inr <$> List.length <$> many (tk ",")
  let which
    ←-- empty columns
      p
  match which with
    | Sum.inl l => do
      let h::tl ← pure l
      let n := h
      let l : List (Vector α n) ←
        l fun row =>
            if h : row = n then pure (⟨row, h⟩ : Vector α n)
            else interaction_monad.fail "Rows must be of equal length"
      pure ⟨l, n, fun i j => (l _ i).get? j⟩
    | Sum.inr n => pure ⟨0, n, finZeroElim⟩
#align matrix.entry_parser matrix.entry_parser

-- Lean can't find this instance without some help. We only need it available in `Type 0`, and it is
-- a massive amount of effort to make it universe-polymorphic.
@[instance]
unsafe def sigma_sigma_fin_matrix_has_reflect {α : Type} [has_reflect α] [reflected _ α] :
    has_reflect (Σm n : ℕ, Fin m → Fin n → α) :=
  @sigma.reflect.{0, 0} _ _ ℕ (fun m => Σn, Fin m → Fin n → α) _ _ _ fun i =>
    @sigma.reflect.{0, 0} _ _ ℕ _ _ _ _ fun j => inferInstance
#align matrix.sigma_sigma_fin_matrix_has_reflect matrix.sigma_sigma_fin_matrix_has_reflect

/-- `!![a, b; c, d]` notation for matrices indexed by `fin m` and `fin n`. See the module docstring
for details. -/
@[user_notation]
unsafe def notation (_ : parse <| tk "!![")
    (val : parse (entry_parser (parser.pexpr 1) <* tk "]")) : parser pexpr := do
  let ⟨m, n, entries⟩ := val
  let entry_vals := pi_fin.to_pexpr (pi_fin.to_pexpr ∘ entries)
  pure (``(@Matrix.of (Fin $(q(m))) (Fin $(q(n))) _).app entry_vals)
#align matrix.notation matrix.notation

end Parser

variable (a b : ℕ)

/-- Use `![...]` notation for displaying a `fin`-indexed matrix, for example:

```
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]
```
-/
instance [Repr α] : Repr (Matrix (Fin m) (Fin n) α)
    where repr f :=
    "!![" ++
        (String.intercalate "; " <|
          (List.finRange m).map fun i =>
            String.intercalate ", " <| (List.finRange n).map fun j => repr (f i j)) ++
      "]"

#print Matrix.cons_val' /-
@[simp]
theorem cons_val' (v : n' → α) (B : Fin m → n' → α) (i j) :
    vecCons v B i j = vecCons (v j) (fun i => B i j) i := by refine' Fin.cases _ _ i <;> simp
#align matrix.cons_val' Matrix.cons_val'
-/

#print Matrix.head_val' /-
@[simp]
theorem head_val' (B : Fin m.succ → n' → α) (j : n') : (vecHead fun i => B i j) = vecHead B j :=
  rfl
#align matrix.head_val' Matrix.head_val'
-/

#print Matrix.tail_val' /-
@[simp]
theorem tail_val' (B : Fin m.succ → n' → α) (j : n') :
    (vecTail fun i => B i j) = fun i => vecTail B i j :=
  by
  ext
  simp [vec_tail]
#align matrix.tail_val' Matrix.tail_val'
-/

section DotProduct

variable [AddCommMonoid α] [Mul α]

/- warning: matrix.dot_product_empty -> Matrix.dotProduct_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (v : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α) (w : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α (Fin.fintype (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) _inst_2 _inst_1 v w) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (v : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) (w : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α (Fin.fintype (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) _inst_2 _inst_1 v w) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_empty Matrix.dotProduct_emptyₓ'. -/
@[simp]
theorem dotProduct_empty (v w : Fin 0 → α) : dotProduct v w = 0 :=
  Finset.sum_empty
#align matrix.dot_product_empty Matrix.dotProduct_empty

/- warning: matrix.cons_dot_product -> Matrix.cons_dotProduct is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (x : α) (v : (Fin n) -> α) (w : (Fin (Nat.succ n)) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (Nat.succ n)) α (Fin.fintype (Nat.succ n)) _inst_2 _inst_1 (Matrix.vecCons.{u1} α n x v) w) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x (Matrix.vecHead.{u1} α n w)) (Matrix.dotProduct.{u1, 0} (Fin n) α (Fin.fintype n) _inst_2 _inst_1 v (Matrix.vecTail.{u1} α n w)))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (x : α) (v : (Fin n) -> α) (w : (Fin (Nat.succ n)) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (Nat.succ n)) α (Fin.fintype (Nat.succ n)) _inst_2 _inst_1 (Matrix.vecCons.{u1} α n x v) w) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x (Matrix.vecHead.{u1} α n w)) (Matrix.dotProduct.{u1, 0} (Fin n) α (Fin.fintype n) _inst_2 _inst_1 v (Matrix.vecTail.{u1} α n w)))
Case conversion may be inaccurate. Consider using '#align matrix.cons_dot_product Matrix.cons_dotProductₓ'. -/
@[simp]
theorem cons_dotProduct (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    dotProduct (vecCons x v) w = x * vecHead w + dotProduct v (vecTail w) := by
  simp [dot_product, Fin.sum_univ_succ, vec_head, vec_tail]
#align matrix.cons_dot_product Matrix.cons_dotProduct

/- warning: matrix.dot_product_cons -> Matrix.dotProduct_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (v : (Fin (Nat.succ n)) -> α) (x : α) (w : (Fin n) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (Nat.succ n)) α (Fin.fintype (Nat.succ n)) _inst_2 _inst_1 v (Matrix.vecCons.{u1} α n x w)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (Matrix.vecHead.{u1} α n v) x) (Matrix.dotProduct.{u1, 0} (Fin n) α (Fin.fintype n) _inst_2 _inst_1 (Matrix.vecTail.{u1} α n v) w))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (v : (Fin (Nat.succ n)) -> α) (x : α) (w : (Fin n) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (Nat.succ n)) α (Fin.fintype (Nat.succ n)) _inst_2 _inst_1 v (Matrix.vecCons.{u1} α n x w)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (Matrix.vecHead.{u1} α n v) x) (Matrix.dotProduct.{u1, 0} (Fin n) α (Fin.fintype n) _inst_2 _inst_1 (Matrix.vecTail.{u1} α n v) w))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_cons Matrix.dotProduct_consₓ'. -/
@[simp]
theorem dotProduct_cons (v : Fin n.succ → α) (x : α) (w : Fin n → α) :
    dotProduct v (vecCons x w) = vecHead v * x + dotProduct (vecTail v) w := by
  simp [dot_product, Fin.sum_univ_succ, vec_head, vec_tail]
#align matrix.dot_product_cons Matrix.dotProduct_cons

/- warning: matrix.cons_dot_product_cons -> Matrix.cons_dotProduct_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (x : α) (v : (Fin n) -> α) (y : α) (w : (Fin n) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (Nat.succ n)) α (Fin.fintype (Nat.succ n)) _inst_2 _inst_1 (Matrix.vecCons.{u1} α n x v) (Matrix.vecCons.{u1} α n y w)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x y) (Matrix.dotProduct.{u1, 0} (Fin n) α (Fin.fintype n) _inst_2 _inst_1 v w))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (x : α) (v : (Fin n) -> α) (y : α) (w : (Fin n) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (Nat.succ n)) α (Fin.fintype (Nat.succ n)) _inst_2 _inst_1 (Matrix.vecCons.{u1} α n x v) (Matrix.vecCons.{u1} α n y w)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x y) (Matrix.dotProduct.{u1, 0} (Fin n) α (Fin.fintype n) _inst_2 _inst_1 v w))
Case conversion may be inaccurate. Consider using '#align matrix.cons_dot_product_cons Matrix.cons_dotProduct_consₓ'. -/
@[simp]
theorem cons_dotProduct_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    dotProduct (vecCons x v) (vecCons y w) = x * y + dotProduct v w := by simp
#align matrix.cons_dot_product_cons Matrix.cons_dotProduct_cons

end DotProduct

section ColRow

#print Matrix.col_empty /-
@[simp]
theorem col_empty (v : Fin 0 → α) : col v = vecEmpty :=
  empty_eq _
#align matrix.col_empty Matrix.col_empty
-/

#print Matrix.col_cons /-
@[simp]
theorem col_cons (x : α) (u : Fin m → α) : col (vecCons x u) = vecCons (fun _ => x) (col u) :=
  by
  ext (i j)
  refine' Fin.cases _ _ i <;> simp [vec_head, vec_tail]
#align matrix.col_cons Matrix.col_cons
-/

#print Matrix.row_empty /-
@[simp]
theorem row_empty : row (vecEmpty : Fin 0 → α) = fun _ => vecEmpty :=
  by
  ext
  rfl
#align matrix.row_empty Matrix.row_empty
-/

#print Matrix.row_cons /-
@[simp]
theorem row_cons (x : α) (u : Fin m → α) : row (vecCons x u) = fun _ => vecCons x u :=
  by
  ext
  rfl
#align matrix.row_cons Matrix.row_cons
-/

end ColRow

section Transpose

#print Matrix.transpose_empty_rows /-
@[simp]
theorem transpose_empty_rows (A : Matrix m' (Fin 0) α) : Aᵀ = of ![] :=
  empty_eq _
#align matrix.transpose_empty_rows Matrix.transpose_empty_rows
-/

#print Matrix.transpose_empty_cols /-
@[simp]
theorem transpose_empty_cols (A : Matrix (Fin 0) m' α) : Aᵀ = of fun i => ![] :=
  funext fun i => empty_eq _
#align matrix.transpose_empty_cols Matrix.transpose_empty_cols
-/

#print Matrix.cons_transpose /-
@[simp]
theorem cons_transpose (v : n' → α) (A : Matrix (Fin m) n' α) :
    (of (vecCons v A))ᵀ = of fun i => vecCons (v i) (Aᵀ i) :=
  by
  ext (i j)
  refine' Fin.cases _ _ j <;> simp
#align matrix.cons_transpose Matrix.cons_transpose
-/

#print Matrix.head_transpose /-
@[simp]
theorem head_transpose (A : Matrix m' (Fin n.succ) α) :
    vecHead (of.symm Aᵀ) = vecHead ∘ of.symm A :=
  rfl
#align matrix.head_transpose Matrix.head_transpose
-/

#print Matrix.tail_transpose /-
@[simp]
theorem tail_transpose (A : Matrix m' (Fin n.succ) α) : vecTail (of.symm Aᵀ) = (vecTail ∘ A)ᵀ :=
  by
  ext (i j)
  rfl
#align matrix.tail_transpose Matrix.tail_transpose
-/

end Transpose

section Mul

variable [Semiring α]

/- warning: matrix.empty_mul -> Matrix.empty_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n' : Type.{u2}} {o' : Type.{u3}} [_inst_1 : Semiring.{u1} α] [_inst_2 : Fintype.{u2} n'] (A : Matrix.{0, u2, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) n' α) (B : Matrix.{u2, u3, u1} n' o' α), Eq.{succ (max u3 u1)} (Matrix.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) o' α) (Matrix.mul.{u1, 0, u2, u3} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) n' o' α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) A B) (coeFn.{max 1 (max (max 1 (succ u3) (succ u1)) (succ (max u3 u1))) (succ (max u3 u1)) 1 (succ u3) (succ u1), max (max 1 (succ u3) (succ u1)) (succ (max u3 u1))} (Equiv.{max 1 (succ u3) (succ u1), succ (max u3 u1)} ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> o' -> α) (Matrix.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) o' α)) (fun (_x : Equiv.{max 1 (succ u3) (succ u1), succ (max u3 u1)} ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> o' -> α) (Matrix.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) o' α)) => ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> o' -> α) -> (Matrix.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) o' α)) (Equiv.hasCoeToFun.{max 1 (succ u3) (succ u1), succ (max u3 u1)} ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> o' -> α) (Matrix.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) o' α)) (Matrix.of.{u1, 0, u3} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) o' α) (Matrix.vecEmpty.{max u3 u1} (o' -> α)))
but is expected to have type
  forall {α : Type.{u1}} {n' : Type.{u2}} {o' : Type.{u3}} [_inst_1 : Semiring.{u1} α] [_inst_2 : Fintype.{u2} n'] (A : Matrix.{0, u2, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) n' α) (B : Matrix.{u2, u3, u1} n' o' α), Eq.{max (succ u1) (succ u3)} (Matrix.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) o' α) (Matrix.mul.{u1, 0, u2, u3} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) n' o' α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) A B) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u1) (succ u3), max (max (succ u1) (succ u3)) 1} ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> o' -> α) (Matrix.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) o' α)) ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> o' -> α) (fun (_x : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> o' -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> o' -> α) => Matrix.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) o' α) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> o' -> α) (Matrix.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) o' α)) (Matrix.of.{u1, 0, u3} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) o' α) (Matrix.vecEmpty.{max u3 u1} (o' -> α)))
Case conversion may be inaccurate. Consider using '#align matrix.empty_mul Matrix.empty_mulₓ'. -/
@[simp]
theorem empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : Matrix n' o' α) : A ⬝ B = of ![] :=
  empty_eq _
#align matrix.empty_mul Matrix.empty_mul

/- warning: matrix.empty_mul_empty -> Matrix.empty_mul_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m' : Type.{u2}} {o' : Type.{u3}} [_inst_1 : Semiring.{u1} α] (A : Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α) (B : Matrix.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) o' α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m' o' α) (Matrix.mul.{u1, u2, 0, u3} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) o' α (Fin.fintype (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) A B) (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} m' o' α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} m' o' α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} m' o' α) (Matrix.hasZero.{u1, u2, u3} m' o' α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} {m' : Type.{u2}} {o' : Type.{u3}} [_inst_1 : Semiring.{u1} α] (A : Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α) (B : Matrix.{0, u3, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) o' α), Eq.{max (max (succ u1) (succ u3)) (succ u2)} (Matrix.{u2, u3, u1} m' o' α) (Matrix.mul.{u1, u2, 0, u3} m' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) o' α (Fin.fintype (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) A B) (OfNat.ofNat.{max (max u1 u3) u2} (Matrix.{u2, u3, u1} m' o' α) 0 (Zero.toOfNat0.{max (max u1 u3) u2} (Matrix.{u2, u3, u1} m' o' α) (Matrix.zero.{u1, u2, u3} m' o' α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.empty_mul_empty Matrix.empty_mul_emptyₓ'. -/
@[simp]
theorem empty_mul_empty (A : Matrix m' (Fin 0) α) (B : Matrix (Fin 0) o' α) : A ⬝ B = 0 :=
  rfl
#align matrix.empty_mul_empty Matrix.empty_mul_empty

/- warning: matrix.mul_empty -> Matrix.mul_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m' : Type.{u2}} {n' : Type.{u3}} [_inst_1 : Semiring.{u1} α] [_inst_2 : Fintype.{u3} n'] (A : Matrix.{u2, u3, u1} m' n' α) (B : Matrix.{u3, 0, u1} n' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α), Eq.{succ (max u2 u1)} (Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α) (Matrix.mul.{u1, u2, u3, 0} m' n' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) A B) (coeFn.{max 1 (max (max (succ u2) (succ u1)) (succ (max u2 u1))) (succ (max u2 u1)) (succ u2) (succ u1), max (max (succ u2) (succ u1)) (succ (max u2 u1))} (Equiv.{max (succ u2) (succ u1), succ (max u2 u1)} (m' -> (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α) (Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α)) (fun (_x : Equiv.{max (succ u2) (succ u1), succ (max u2 u1)} (m' -> (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α) (Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α)) => (m' -> (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α) -> (Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u1), succ (max u2 u1)} (m' -> (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α) (Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α)) (Matrix.of.{u1, u2, 0} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α) (fun (_x : m') => Matrix.vecEmpty.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {m' : Type.{u2}} {n' : Type.{u3}} [_inst_1 : Semiring.{u1} α] [_inst_2 : Fintype.{u3} n'] (A : Matrix.{u2, u3, u1} m' n' α) (B : Matrix.{u3, 0, u1} n' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α), Eq.{max (succ u1) (succ u2)} (Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α) (Matrix.mul.{u1, u2, u3, 0} m' n' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) A B) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (max (succ u1) (succ u2)) 1, max (succ u1) (succ u2)} (m' -> (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) (Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α)) (m' -> (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) (fun (_x : m' -> (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m' -> (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) => Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (m' -> (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) (Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α)) (Matrix.of.{u1, u2, 0} m' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α) (fun (_x : m') => Matrix.vecEmpty.{u1} α))
Case conversion may be inaccurate. Consider using '#align matrix.mul_empty Matrix.mul_emptyₓ'. -/
@[simp]
theorem mul_empty [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Fin 0) α) :
    A ⬝ B = of fun _ => ![] :=
  funext fun _ => empty_eq _
#align matrix.mul_empty Matrix.mul_empty

/- warning: matrix.mul_val_succ -> Matrix.mul_val_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Nat} {n' : Type.{u2}} {o' : Type.{u3}} [_inst_1 : Semiring.{u1} α] [_inst_2 : Fintype.{u2} n'] (A : Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) (B : Matrix.{u2, u3, u1} n' o' α) (i : Fin m) (j : o'), Eq.{succ u1} α (Matrix.mul.{u1, 0, u2, u3} (Fin (Nat.succ m)) n' o' α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) A B (Fin.succ m i) j) (Matrix.mul.{u1, 0, u2, u3} (Fin m) n' o' α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (coeFn.{max 1 (max (max 1 (succ u2) (succ u1)) (succ (max u2 u1))) (succ (max u2 u1)) 1 (succ u2) (succ u1), max (max 1 (succ u2) (succ u1)) (succ (max u2 u1))} (Equiv.{max 1 (succ u2) (succ u1), succ (max u2 u1)} ((Fin m) -> n' -> α) (Matrix.{0, u2, u1} (Fin m) n' α)) (fun (_x : Equiv.{max 1 (succ u2) (succ u1), succ (max u2 u1)} ((Fin m) -> n' -> α) (Matrix.{0, u2, u1} (Fin m) n' α)) => ((Fin m) -> n' -> α) -> (Matrix.{0, u2, u1} (Fin m) n' α)) (Equiv.hasCoeToFun.{max 1 (succ u2) (succ u1), succ (max u2 u1)} ((Fin m) -> n' -> α) (Matrix.{0, u2, u1} (Fin m) n' α)) (Matrix.of.{u1, 0, u2} (Fin m) n' α) (Matrix.vecTail.{max u2 u1} (n' -> α) m (coeFn.{max 1 (max (succ (max u2 u1)) 1 (succ u2) (succ u1)) (max 1 (succ u2) (succ u1)) (succ (max u2 u1)), max (succ (max u2 u1)) 1 (succ u2) (succ u1)} (Equiv.{succ (max u2 u1), max 1 (succ u2) (succ u1)} (Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) ((Fin (Nat.succ m)) -> n' -> α)) (fun (_x : Equiv.{succ (max u2 u1), max 1 (succ u2) (succ u1)} (Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) ((Fin (Nat.succ m)) -> n' -> α)) => (Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) -> (Fin (Nat.succ m)) -> n' -> α) (Equiv.hasCoeToFun.{succ (max u2 u1), max 1 (succ u2) (succ u1)} (Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) ((Fin (Nat.succ m)) -> n' -> α)) (Equiv.symm.{max 1 (succ u2) (succ u1), succ (max u2 u1)} ((Fin (Nat.succ m)) -> n' -> α) (Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) (Matrix.of.{u1, 0, u2} (Fin (Nat.succ m)) n' α)) A))) B i j)
but is expected to have type
  forall {α : Type.{u1}} {m : Nat} {n' : Type.{u2}} {o' : Type.{u3}} [_inst_1 : Semiring.{u1} α] [_inst_2 : Fintype.{u2} n'] (A : Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) (B : Matrix.{u2, u3, u1} n' o' α) (i : Fin m) (j : o'), Eq.{succ u1} α (Matrix.mul.{u1, 0, u2, u3} (Fin (Nat.succ m)) n' o' α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) A B (Fin.succ m i) j) (Matrix.mul.{u1, 0, u2, u3} (Fin m) n' o' α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (max (succ u1) (succ u2)) 1} ((Fin m) -> n' -> α) (Matrix.{0, u2, u1} (Fin m) n' α)) ((Fin m) -> n' -> α) (fun (_x : (Fin m) -> n' -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : (Fin m) -> n' -> α) => Matrix.{0, u2, u1} (Fin m) n' α) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} ((Fin m) -> n' -> α) (Matrix.{0, u2, u1} (Fin m) n' α)) (Matrix.of.{u1, 0, u2} (Fin m) n' α) (Matrix.vecTail.{max u2 u1} (n' -> α) m (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) ((Fin (Nat.succ m)) -> n' -> α)) (Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) (fun (_x : Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) => (Fin (Nat.succ m)) -> n' -> α) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) ((Fin (Nat.succ m)) -> n' -> α)) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} ((Fin (Nat.succ m)) -> n' -> α) (Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) (Matrix.of.{u1, 0, u2} (Fin (Nat.succ m)) n' α)) A))) B i j)
Case conversion may be inaccurate. Consider using '#align matrix.mul_val_succ Matrix.mul_val_succₓ'. -/
theorem mul_val_succ [Fintype n'] (A : Matrix (Fin m.succ) n' α) (B : Matrix n' o' α) (i : Fin m)
    (j : o') : (A ⬝ B) i.succ j = (of (vecTail (of.symm A)) ⬝ B) i j :=
  rfl
#align matrix.mul_val_succ Matrix.mul_val_succ

#print Matrix.cons_mul /-
@[simp]
theorem cons_mul [Fintype n'] (v : n' → α) (A : Fin m → n' → α) (B : Matrix n' o' α) :
    of (vecCons v A) ⬝ B = of (vecCons (vecMul v B) (of.symm (of A ⬝ B))) :=
  by
  ext (i j)
  refine' Fin.cases _ _ i
  · rfl
  simp [mul_val_succ]
#align matrix.cons_mul Matrix.cons_mul
-/

end Mul

section VecMul

variable [Semiring α]

/- warning: matrix.empty_vec_mul -> Matrix.empty_vecMul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {o' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (v : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α) (B : Matrix.{0, u2, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) o' α), Eq.{max (succ u2) (succ u1)} (o' -> α) (Matrix.vecMul.{u1, 0, u2} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) o' α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)) (Fin.fintype (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) v B) (OfNat.ofNat.{max u2 u1} (o' -> α) 0 (OfNat.mk.{max u2 u1} (o' -> α) 0 (Zero.zero.{max u2 u1} (o' -> α) (Pi.instZero.{u2, u1} o' (fun (ᾰ : o') => α) (fun (i : o') => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} {o' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (v : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) (B : Matrix.{0, u2, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) o' α), Eq.{max (succ u1) (succ u2)} (o' -> α) (Matrix.vecMul.{u1, 0, u2} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) o' α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)) (Fin.fintype (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) v B) (OfNat.ofNat.{max u1 u2} (o' -> α) 0 (Zero.toOfNat0.{max u1 u2} (o' -> α) (Pi.instZero.{u2, u1} o' (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18132 : o') => α) (fun (i : o') => MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.empty_vec_mul Matrix.empty_vecMulₓ'. -/
@[simp]
theorem empty_vecMul (v : Fin 0 → α) (B : Matrix (Fin 0) o' α) : vecMul v B = 0 :=
  rfl
#align matrix.empty_vec_mul Matrix.empty_vecMul

#print Matrix.vecMul_empty /-
@[simp]
theorem vecMul_empty [Fintype n'] (v : n' → α) (B : Matrix n' (Fin 0) α) : vecMul v B = ![] :=
  empty_eq _
#align matrix.vec_mul_empty Matrix.vecMul_empty
-/

#print Matrix.cons_vecMul /-
@[simp]
theorem cons_vecMul (x : α) (v : Fin n → α) (B : Fin n.succ → o' → α) :
    vecMul (vecCons x v) (of B) = x • vecHead B + vecMul v (of <| vecTail B) :=
  by
  ext i
  simp [vec_mul]
#align matrix.cons_vec_mul Matrix.cons_vecMul
-/

#print Matrix.vecMul_cons /-
@[simp]
theorem vecMul_cons (v : Fin n.succ → α) (w : o' → α) (B : Fin n → o' → α) :
    vecMul v (of <| vecCons w B) = vecHead v • w + vecMul (vecTail v) (of B) :=
  by
  ext i
  simp [vec_mul]
#align matrix.vec_mul_cons Matrix.vecMul_cons
-/

#print Matrix.cons_vecMul_cons /-
@[simp]
theorem cons_vecMul_cons (x : α) (v : Fin n → α) (w : o' → α) (B : Fin n → o' → α) :
    vecMul (vecCons x v) (of <| vecCons w B) = x • w + vecMul v (of B) := by simp
#align matrix.cons_vec_mul_cons Matrix.cons_vecMul_cons
-/

end VecMul

section MulVec

variable [Semiring α]

#print Matrix.empty_mulVec /-
@[simp]
theorem empty_mulVec [Fintype n'] (A : Matrix (Fin 0) n' α) (v : n' → α) : mulVec A v = ![] :=
  empty_eq _
#align matrix.empty_mul_vec Matrix.empty_mulVec
-/

/- warning: matrix.mul_vec_empty -> Matrix.mulVec_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (A : Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α) (v : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α), Eq.{max (succ u2) (succ u1)} (m' -> α) (Matrix.mulVec.{u1, u2, 0} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)) (Fin.fintype (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) A v) (OfNat.ofNat.{max u2 u1} (m' -> α) 0 (OfNat.mk.{max u2 u1} (m' -> α) 0 (Zero.zero.{max u2 u1} (m' -> α) (Pi.instZero.{u2, u1} m' (fun (ᾰ : m') => α) (fun (i : m') => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} {m' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (A : Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α) (v : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α), Eq.{max (succ u1) (succ u2)} (m' -> α) (Matrix.mulVec.{u1, u2, 0} m' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)) (Fin.fintype (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) A v) (OfNat.ofNat.{max u1 u2} (m' -> α) 0 (Zero.toOfNat0.{max u1 u2} (m' -> α) (Pi.instZero.{u2, u1} m' (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18074 : m') => α) (fun (i : m') => MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_empty Matrix.mulVec_emptyₓ'. -/
@[simp]
theorem mulVec_empty (A : Matrix m' (Fin 0) α) (v : Fin 0 → α) : mulVec A v = 0 :=
  rfl
#align matrix.mul_vec_empty Matrix.mulVec_empty

#print Matrix.cons_mulVec /-
@[simp]
theorem cons_mulVec [Fintype n'] (v : n' → α) (A : Fin m → n' → α) (w : n' → α) :
    mulVec (of <| vecCons v A) w = vecCons (dotProduct v w) (mulVec (of A) w) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp [mul_vec]
#align matrix.cons_mul_vec Matrix.cons_mulVec
-/

/- warning: matrix.mul_vec_cons -> Matrix.mulVec_cons is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {m' : Type.{u1}} {α : Type.{u2}} [_inst_2 : CommSemiring.{u2} α] (A : m' -> (Fin (Nat.succ n)) -> α) (x : α) (v : (Fin n) -> α), Eq.{max (succ u1) (succ u2)} (m' -> α) (Matrix.mulVec.{u2, u1, 0} m' (Fin (Nat.succ n)) α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_2))) (Fin.fintype (Nat.succ n)) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ (max u1 u2))) (succ (max u1 u2)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ (max u1 u2))} (Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (m' -> (Fin (Nat.succ n)) -> α) (Matrix.{u1, 0, u2} m' (Fin (Nat.succ n)) α)) (fun (_x : Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (m' -> (Fin (Nat.succ n)) -> α) (Matrix.{u1, 0, u2} m' (Fin (Nat.succ n)) α)) => (m' -> (Fin (Nat.succ n)) -> α) -> (Matrix.{u1, 0, u2} m' (Fin (Nat.succ n)) α)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), succ (max u1 u2)} (m' -> (Fin (Nat.succ n)) -> α) (Matrix.{u1, 0, u2} m' (Fin (Nat.succ n)) α)) (Matrix.of.{u2, u1, 0} m' (Fin (Nat.succ n)) α) A) (Matrix.vecCons.{u2} α n x v)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (m' -> α) (m' -> α) (m' -> α) (instHAdd.{max u1 u2} (m' -> α) (Pi.instAdd.{u1, u2} m' (fun (ᾰ : m') => α) (fun (i : m') => Distrib.toHasAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_2))))))) (SMul.smul.{u2, max u1 u2} α (m' -> α) (Function.hasSMul.{u1, u2, u2} m' α α (Mul.toSMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_2))))))) x (Function.comp.{succ u1, succ u2, succ u2} m' ((Fin (Nat.succ n)) -> α) α (Matrix.vecHead.{u2} α n) A)) (Matrix.mulVec.{u2, u1, 0} m' (Fin n) α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_2))) (Fin.fintype n) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ (max u1 u2))) (succ (max u1 u2)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ (max u1 u2))} (Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (m' -> (Fin n) -> α) (Matrix.{u1, 0, u2} m' (Fin n) α)) (fun (_x : Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (m' -> (Fin n) -> α) (Matrix.{u1, 0, u2} m' (Fin n) α)) => (m' -> (Fin n) -> α) -> (Matrix.{u1, 0, u2} m' (Fin n) α)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), succ (max u1 u2)} (m' -> (Fin n) -> α) (Matrix.{u1, 0, u2} m' (Fin n) α)) (Matrix.of.{u2, u1, 0} m' (Fin n) α) (Function.comp.{succ u1, succ u2, succ u2} m' ((Fin (Nat.succ n)) -> α) ((Fin n) -> α) (Matrix.vecTail.{u2} α n) A)) v))
but is expected to have type
  forall {n : Nat} {m' : Type.{u2}} {α : Type.{u1}} [_inst_2 : CommSemiring.{u1} α] (A : m' -> (Fin (Nat.succ n)) -> α) (x : α) (v : (Fin n) -> α), Eq.{max (succ u2) (succ u1)} (m' -> α) (Matrix.mulVec.{u1, u2, 0} m' (Fin (Nat.succ n)) α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2))) (Fin.fintype (Nat.succ n)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (max (succ u1) (succ u2)) 1, max (succ u1) (succ u2)} (m' -> (Fin (Nat.succ n)) -> α) (Matrix.{u2, 0, u1} m' (Fin (Nat.succ n)) α)) (m' -> (Fin (Nat.succ n)) -> α) (fun (_x : m' -> (Fin (Nat.succ n)) -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m' -> (Fin (Nat.succ n)) -> α) => Matrix.{u2, 0, u1} m' (Fin (Nat.succ n)) α) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (m' -> (Fin (Nat.succ n)) -> α) (Matrix.{u2, 0, u1} m' (Fin (Nat.succ n)) α)) (Matrix.of.{u1, u2, 0} m' (Fin (Nat.succ n)) α) A) (Matrix.vecCons.{u1} α n x v)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m' -> α) (m' -> α) (m' -> α) (instHAdd.{max u2 u1} (m' -> α) (Pi.instAdd.{u2, u1} m' (fun (ᾰ : m') => α) (fun (i : m') => Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2))))))) (HSMul.hSMul.{u1, max u2 u1, max u2 u1} α (m' -> α) (m' -> α) (instHSMul.{u1, max u2 u1} α (m' -> α) (Pi.instSMul.{u2, u1, u1} m' α (fun (a._@.Init.Prelude._hyg.25 : m') => α) (fun (i : m') => Algebra.toSMul.{u1, u1} α α _inst_2 (CommSemiring.toSemiring.{u1} α _inst_2) (Algebra.id.{u1} α _inst_2)))) x (Function.comp.{succ u2, succ u1, succ u1} m' ((Fin (Nat.succ n)) -> α) α (Matrix.vecHead.{u1} α n) A)) (Matrix.mulVec.{u1, u2, 0} m' (Fin n) α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2))) (Fin.fintype n) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (max (succ u1) (succ u2)) 1, max (succ u1) (succ u2)} (m' -> (Fin n) -> α) (Matrix.{u2, 0, u1} m' (Fin n) α)) (m' -> (Fin n) -> α) (fun (_x : m' -> (Fin n) -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m' -> (Fin n) -> α) => Matrix.{u2, 0, u1} m' (Fin n) α) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (m' -> (Fin n) -> α) (Matrix.{u2, 0, u1} m' (Fin n) α)) (Matrix.of.{u1, u2, 0} m' (Fin n) α) (Function.comp.{succ u2, succ u1, succ u1} m' ((Fin (Nat.succ n)) -> α) ((Fin n) -> α) (Matrix.vecTail.{u1} α n) A)) v))
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_cons Matrix.mulVec_consₓ'. -/
@[simp]
theorem mulVec_cons {α} [CommSemiring α] (A : m' → Fin n.succ → α) (x : α) (v : Fin n → α) :
    mulVec (of A) (vecCons x v) = x • vecHead ∘ A + mulVec (of (vecTail ∘ A)) v :=
  by
  ext i
  simp [mul_vec, mul_comm]
#align matrix.mul_vec_cons Matrix.mulVec_cons

end MulVec

section VecMulVec

variable [Semiring α]

/- warning: matrix.empty_vec_mul_vec -> Matrix.empty_vecMulVec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (v : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α) (w : n' -> α), Eq.{succ (max u2 u1)} (Matrix.{0, u2, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) n' α) (Matrix.vecMulVec.{u1, 0, u2} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) n' α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) v w) (Matrix.vecEmpty.{max u2 u1} (n' -> α))
but is expected to have type
  forall {α : Type.{u1}} {n' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (v : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) (w : n' -> α), Eq.{max (succ u1) (succ u2)} (Matrix.{0, u2, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) n' α) (Matrix.vecMulVec.{u1, 0, u2} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) n' α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) v w) (Matrix.vecEmpty.{max u1 u2} (n' -> α))
Case conversion may be inaccurate. Consider using '#align matrix.empty_vec_mul_vec Matrix.empty_vecMulVecₓ'. -/
@[simp]
theorem empty_vecMulVec (v : Fin 0 → α) (w : n' → α) : vecMulVec v w = ![] :=
  empty_eq _
#align matrix.empty_vec_mul_vec Matrix.empty_vecMulVec

/- warning: matrix.vec_mul_vec_empty -> Matrix.vecMulVec_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (v : m' -> α) (w : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α) (Matrix.vecMulVec.{u1, u2, 0} m' (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) v w) (fun (_x : m') => Matrix.vecEmpty.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {m' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (v : m' -> α) (w : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α), Eq.{max (succ u1) (succ u2)} (Matrix.{u2, 0, u1} m' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α) (Matrix.vecMulVec.{u1, u2, 0} m' (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) v w) (fun (_x : m') => Matrix.vecEmpty.{u1} α)
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_vec_empty Matrix.vecMulVec_emptyₓ'. -/
@[simp]
theorem vecMulVec_empty (v : m' → α) (w : Fin 0 → α) : vecMulVec v w = fun _ => ![] :=
  funext fun i => empty_eq _
#align matrix.vec_mul_vec_empty Matrix.vecMulVec_empty

/- warning: matrix.cons_vec_mul_vec -> Matrix.cons_vecMulVec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Nat} {n' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (x : α) (v : (Fin m) -> α) (w : n' -> α), Eq.{succ (max u2 u1)} (Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) (Matrix.vecMulVec.{u1, 0, u2} (Fin (Nat.succ m)) n' α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (Matrix.vecCons.{u1} α m x v) w) (Matrix.vecCons.{max u2 u1} (n' -> α) m (SMul.smul.{u1, max u2 u1} α (n' -> α) (Function.hasSMul.{u2, u1, u1} n' α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))) x w) (Matrix.vecMulVec.{u1, 0, u2} (Fin m) n' α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) v w))
but is expected to have type
  forall {α : Type.{u1}} {m : Nat} {n' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (x : α) (v : (Fin m) -> α) (w : n' -> α), Eq.{max (succ u1) (succ u2)} (Matrix.{0, u2, u1} (Fin (Nat.succ m)) n' α) (Matrix.vecMulVec.{u1, 0, u2} (Fin (Nat.succ m)) n' α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Matrix.vecCons.{u1} α m x v) w) (Matrix.vecCons.{max u1 u2} (n' -> α) m (HSMul.hSMul.{u1, max u1 u2, max u1 u2} α (n' -> α) (n' -> α) (instHSMul.{u1, max u1 u2} α (n' -> α) (Pi.instSMul.{u2, u1, u1} n' α (fun (a._@.Mathlib.Data.Matrix.Notation._hyg.4067 : n') => α) (fun (i : n') => SMulZeroClass.toSMul.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (MulZeroClass.toSMulWithZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))) x w) (Matrix.vecMulVec.{u1, 0, u2} (Fin m) n' α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) v w))
Case conversion may be inaccurate. Consider using '#align matrix.cons_vec_mul_vec Matrix.cons_vecMulVecₓ'. -/
@[simp]
theorem cons_vecMulVec (x : α) (v : Fin m → α) (w : n' → α) :
    vecMulVec (vecCons x v) w = vecCons (x • w) (vecMulVec v w) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp [vec_mul_vec]
#align matrix.cons_vec_mul_vec Matrix.cons_vecMulVec

/- warning: matrix.vec_mul_vec_cons -> Matrix.vecMulVec_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} {m' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (v : m' -> α) (x : α) (w : (Fin n) -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, 0, u1} m' (Fin (Nat.succ n)) α) (Matrix.vecMulVec.{u1, u2, 0} m' (Fin (Nat.succ n)) α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) v (Matrix.vecCons.{u1} α n x w)) (fun (i : m') => SMul.smul.{u1, u1} α ((Fin (Nat.succ n)) -> α) (Function.hasSMul.{0, u1, u1} (Fin (Nat.succ n)) α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))) (v i) (Matrix.vecCons.{u1} α n x w))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} {m' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (v : m' -> α) (x : α) (w : (Fin n) -> α), Eq.{max (succ u1) (succ u2)} (Matrix.{u2, 0, u1} m' (Fin (Nat.succ n)) α) (Matrix.vecMulVec.{u1, u2, 0} m' (Fin (Nat.succ n)) α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) v (Matrix.vecCons.{u1} α n x w)) (fun (i : m') => HSMul.hSMul.{u1, u1, u1} α ((Fin (Nat.succ n)) -> α) ((Fin (Nat.succ n)) -> α) (instHSMul.{u1, u1} α ((Fin (Nat.succ n)) -> α) (Pi.instSMul.{0, u1, u1} (Fin (Nat.succ n)) α (fun (a._@.Mathlib.Data.Fin.VecNotation._hyg.29 : Fin (Nat.succ n)) => α) (fun (i : Fin (Nat.succ n)) => SMulZeroClass.toSMul.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (MulZeroClass.toSMulWithZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))) (v i) (Matrix.vecCons.{u1} α n x w))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_vec_cons Matrix.vecMulVec_consₓ'. -/
@[simp]
theorem vecMulVec_cons (v : m' → α) (x : α) (w : Fin n → α) :
    vecMulVec v (vecCons x w) = fun i => v i • vecCons x w :=
  by
  ext (i j)
  rw [vec_mul_vec_apply, Pi.smul_apply, smul_eq_mul]
#align matrix.vec_mul_vec_cons Matrix.vecMulVec_cons

end VecMulVec

section Smul

variable [Semiring α]

/- warning: matrix.smul_mat_empty -> Matrix.smul_mat_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m' : Type.{u2}} (x : α) (A : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> m' -> α), Eq.{succ (max u2 u1)} ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> m' -> α) (SMul.smul.{u1, max u2 u1} α ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> m' -> α) (Function.hasSMul.{0, u1, max u2 u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) α (m' -> α) (Function.hasSMul.{u2, u1, u1} m' α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))) x A) (Matrix.vecEmpty.{max u2 u1} (m' -> α))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Semiring.{u2} α] {m' : Type.{u1}} (x : α) (A : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> m' -> α), Eq.{max (succ u2) (succ u1)} ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> m' -> α) (HSMul.hSMul.{u2, max u2 u1, max u2 u1} α ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> m' -> α) ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> m' -> α) (instHSMul.{u2, max u2 u1} α ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> m' -> α) (Pi.instSMul.{0, max u2 u1, u2} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) α (fun (a._@.Mathlib.Data.Matrix.Notation._hyg.4255 : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => m' -> α) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Pi.instSMul.{u1, u2, u2} m' α (fun (a._@.Mathlib.Data.Matrix.Notation._hyg.4258 : m') => α) (fun (i : m') => SMulZeroClass.toSMul.{u2, u2} α α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u2, u2} α α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)) (MulZeroClass.toSMulWithZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))))))))) x A) (Matrix.vecEmpty.{max u2 u1} (m' -> α))
Case conversion may be inaccurate. Consider using '#align matrix.smul_mat_empty Matrix.smul_mat_emptyₓ'. -/
@[simp]
theorem smul_mat_empty {m' : Type _} (x : α) (A : Fin 0 → m' → α) : x • A = ![] :=
  empty_eq _
#align matrix.smul_mat_empty Matrix.smul_mat_empty

/- warning: matrix.smul_mat_cons -> Matrix.smul_mat_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Nat} {n' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (x : α) (v : n' -> α) (A : (Fin m) -> n' -> α), Eq.{succ (max u2 u1)} ((Fin (Nat.succ m)) -> n' -> α) (SMul.smul.{u1, max u2 u1} α ((Fin (Nat.succ m)) -> n' -> α) (Function.hasSMul.{0, u1, max u2 u1} (Fin (Nat.succ m)) α (n' -> α) (Function.hasSMul.{u2, u1, u1} n' α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))) x (Matrix.vecCons.{max u2 u1} (n' -> α) m v A)) (Matrix.vecCons.{max u2 u1} (n' -> α) m (SMul.smul.{u1, max u2 u1} α (n' -> α) (Function.hasSMul.{u2, u1, u1} n' α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))) x v) (SMul.smul.{u1, max u2 u1} α ((Fin m) -> n' -> α) (Function.hasSMul.{0, u1, max u2 u1} (Fin m) α (n' -> α) (Function.hasSMul.{u2, u1, u1} n' α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))) x A))
but is expected to have type
  forall {α : Type.{u1}} {m : Nat} {n' : Type.{u2}} [_inst_1 : Semiring.{u1} α] (x : α) (v : n' -> α) (A : (Fin m) -> n' -> α), Eq.{max (succ u1) (succ u2)} ((Fin (Nat.succ m)) -> n' -> α) (HSMul.hSMul.{u1, max u1 u2, max u1 u2} α ((Fin (Nat.succ m)) -> n' -> α) ((Fin (Nat.succ m)) -> n' -> α) (instHSMul.{u1, max u1 u2} α ((Fin (Nat.succ m)) -> n' -> α) (Pi.instSMul.{0, max u1 u2, u1} (Fin (Nat.succ m)) α (fun (a._@.Mathlib.Data.Fin.VecNotation._hyg.29 : Fin (Nat.succ m)) => n' -> α) (fun (i : Fin (Nat.succ m)) => Pi.instSMul.{u2, u1, u1} n' α (fun (a._@.Mathlib.Data.Matrix.Notation._hyg.4297 : n') => α) (fun (i : n') => SMulZeroClass.toSMul.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (MulZeroClass.toSMulWithZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))) x (Matrix.vecCons.{max u1 u2} (n' -> α) m v A)) (Matrix.vecCons.{max u1 u2} (n' -> α) m (HSMul.hSMul.{u1, max u1 u2, max u1 u2} α (n' -> α) (n' -> α) (instHSMul.{u1, max u1 u2} α (n' -> α) (Pi.instSMul.{u2, u1, u1} n' α (fun (a._@.Mathlib.Data.Matrix.Notation._hyg.4297 : n') => α) (fun (i : n') => SMulZeroClass.toSMul.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (MulZeroClass.toSMulWithZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))) x v) (HSMul.hSMul.{u1, max u1 u2, max u1 u2} α ((Fin m) -> n' -> α) ((Fin m) -> n' -> α) (instHSMul.{u1, max u1 u2} α ((Fin m) -> n' -> α) (Pi.instSMul.{0, max u1 u2, u1} (Fin m) α (fun (a._@.Mathlib.Data.Matrix.Notation._hyg.4300 : Fin m) => n' -> α) (fun (i : Fin m) => Pi.instSMul.{u2, u1, u1} n' α (fun (a._@.Mathlib.Data.Matrix.Notation._hyg.4303 : n') => α) (fun (i : n') => SMulZeroClass.toSMul.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (MulZeroClass.toSMulWithZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))) x A))
Case conversion may be inaccurate. Consider using '#align matrix.smul_mat_cons Matrix.smul_mat_consₓ'. -/
@[simp]
theorem smul_mat_cons (x : α) (v : n' → α) (A : Fin m → n' → α) :
    x • vecCons v A = vecCons (x • v) (x • A) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp
#align matrix.smul_mat_cons Matrix.smul_mat_cons

end Smul

section Submatrix

#print Matrix.submatrix_empty /-
@[simp]
theorem submatrix_empty (A : Matrix m' n' α) (row : Fin 0 → m') (col : o' → n') :
    submatrix A row col = ![] :=
  empty_eq _
#align matrix.submatrix_empty Matrix.submatrix_empty
-/

#print Matrix.submatrix_cons_row /-
@[simp]
theorem submatrix_cons_row (A : Matrix m' n' α) (i : m') (row : Fin m → m') (col : o' → n') :
    submatrix A (vecCons i row) col = vecCons (fun j => A i (col j)) (submatrix A row col) :=
  by
  ext (i j)
  refine' Fin.cases _ _ i <;> simp [submatrix]
#align matrix.submatrix_cons_row Matrix.submatrix_cons_row
-/

end Submatrix

section Vec2AndVec3

section One

variable [Zero α] [One α]

/- warning: matrix.one_fin_two -> Matrix.one_fin_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α], Eq.{succ u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α) (OfNat.ofNat.{u1} (Matrix.{0, 0, u1} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) α) 1 (OfNat.mk.{u1} (Matrix.{0, 0, u1} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) α) 1 (One.one.{u1} (Matrix.{0, 0, u1} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) α) (Matrix.hasOne.{u1, 0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) α (fun (a : Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (b : Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) => Fin.decidableEq (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) a b) _inst_1 _inst_2)))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α)) (fun (_x : Equiv.{succ u1, succ u1} ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α)) => ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) -> (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α)) (Equiv.hasCoeToFun.{succ u1, succ u1} ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α)) (Matrix.of.{u1, 0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α) (Matrix.vecCons.{u1} ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_2))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1))) (Matrix.vecEmpty.{u1} α))) (Matrix.vecCons.{u1} ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_2))) (Matrix.vecEmpty.{u1} α))) (Matrix.vecEmpty.{u1} ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α], Eq.{succ u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) α) (OfNat.ofNat.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) α) 1 (One.toOfNat1.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) α) (Matrix.one.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) α (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) _inst_1 _inst_2))) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) α)) ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α) (fun (_x : (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α) => Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) α)) (Matrix.of.{u1, 0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) α) (Matrix.vecCons.{u1} ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_2)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1)) (Matrix.vecEmpty.{u1} α))) (Matrix.vecCons.{u1} ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_2)) (Matrix.vecEmpty.{u1} α))) (Matrix.vecEmpty.{u1} ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α)))))
Case conversion may be inaccurate. Consider using '#align matrix.one_fin_two Matrix.one_fin_twoₓ'. -/
theorem one_fin_two : (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1] :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.one_fin_two Matrix.one_fin_two

/- warning: matrix.one_fin_three -> Matrix.one_fin_three is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α], Eq.{succ u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α) (OfNat.ofNat.{u1} (Matrix.{0, 0, u1} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) α) 1 (OfNat.mk.{u1} (Matrix.{0, 0, u1} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) α) 1 (One.one.{u1} (Matrix.{0, 0, u1} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) α) (Matrix.hasOne.{u1, 0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) α (fun (a : Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (b : Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) => Fin.decidableEq (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) a b) _inst_1 _inst_2)))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} ((Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α)) (fun (_x : Equiv.{succ u1, succ u1} ((Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α)) => ((Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) -> (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α)) (Equiv.hasCoeToFun.{succ u1, succ u1} ((Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α)) (Matrix.of.{u1, 0, 0} (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α) (Matrix.vecCons.{u1} ((Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_2))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1))) (Matrix.vecEmpty.{u1} α)))) (Matrix.vecCons.{u1} ((Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_2))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1))) (Matrix.vecEmpty.{u1} α)))) (Matrix.vecCons.{u1} ((Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_2))) (Matrix.vecEmpty.{u1} α)))) (Matrix.vecEmpty.{u1} ((Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α], Eq.{succ u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) α) (OfNat.ofNat.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) α) 1 (One.toOfNat1.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) α) (Matrix.one.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) α (fun (a : Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (b : Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) a b) _inst_1 _inst_2))) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} ((Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> α) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) α)) ((Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> α) (fun (_x : (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> α) => Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} ((Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> α) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) α)) (Matrix.of.{u1, 0, 0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) α) (Matrix.vecCons.{u1} ((Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> α) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_2)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1)) (Matrix.vecEmpty.{u1} α)))) (Matrix.vecCons.{u1} ((Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> α) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_2)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1)) (Matrix.vecEmpty.{u1} α)))) (Matrix.vecCons.{u1} ((Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> α) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1)) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_2)) (Matrix.vecEmpty.{u1} α)))) (Matrix.vecEmpty.{u1} ((Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> α))))))
Case conversion may be inaccurate. Consider using '#align matrix.one_fin_three Matrix.one_fin_threeₓ'. -/
theorem one_fin_three : (1 : Matrix (Fin 3) (Fin 3) α) = !![1, 0, 0; 0, 1, 0; 0, 0, 1] :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.one_fin_three Matrix.one_fin_three

end One

#print Matrix.eta_fin_two /-
theorem eta_fin_two (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.eta_fin_two Matrix.eta_fin_two
-/

#print Matrix.eta_fin_three /-
theorem eta_fin_three (A : Matrix (Fin 3) (Fin 3) α) :
    A = !![A 0 0, A 0 1, A 0 2; A 1 0, A 1 1, A 1 2; A 2 0, A 2 1, A 2 2] :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> rfl
#align matrix.eta_fin_three Matrix.eta_fin_three
-/

#print Matrix.mul_fin_two /-
theorem mul_fin_two [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] ⬝ !![b₁₁, b₁₂; b₂₁, b₂₂] =
      !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
        a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul, dot_product, Fin.sum_univ_succ]
#align matrix.mul_fin_two Matrix.mul_fin_two
-/

#print Matrix.mul_fin_three /-
theorem mul_fin_three [AddCommMonoid α] [Mul α]
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
    !![a₁₁, a₁₂, a₁₃; a₂₁, a₂₂, a₂₃; a₃₁, a₃₂, a₃₃] ⬝
        !![b₁₁, b₁₂, b₁₃; b₂₁, b₂₂, b₂₃; b₃₁, b₃₂, b₃₃] =
      !![a₁₁ * b₁₁ + a₁₂ * b₂₁ + a₁₃ * b₃₁, a₁₁ * b₁₂ + a₁₂ * b₂₂ + a₁₃ * b₃₂,
          a₁₁ * b₁₃ + a₁₂ * b₂₃ + a₁₃ * b₃₃;
        a₂₁ * b₁₁ + a₂₂ * b₂₁ + a₂₃ * b₃₁, a₂₁ * b₁₂ + a₂₂ * b₂₂ + a₂₃ * b₃₂,
          a₂₁ * b₁₃ + a₂₂ * b₂₃ + a₂₃ * b₃₃;
        a₃₁ * b₁₁ + a₃₂ * b₂₁ + a₃₃ * b₃₁, a₃₁ * b₁₂ + a₃₂ * b₂₂ + a₃₃ * b₃₂,
          a₃₁ * b₁₃ + a₃₂ * b₂₃ + a₃₃ * b₃₃] :=
  by
  ext (i j)
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul, dot_product, Fin.sum_univ_succ, ← add_assoc]
#align matrix.mul_fin_three Matrix.mul_fin_three
-/

#print Matrix.vec2_eq /-
theorem vec2_eq {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) : ![a₀, a₁] = ![b₀, b₁] := by
  subst_vars
#align matrix.vec2_eq Matrix.vec2_eq
-/

#print Matrix.vec3_eq /-
theorem vec3_eq {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
    ![a₀, a₁, a₂] = ![b₀, b₁, b₂] := by subst_vars
#align matrix.vec3_eq Matrix.vec3_eq
-/

#print Matrix.vec2_add /-
theorem vec2_add [Add α] (a₀ a₁ b₀ b₁ : α) : ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁] := by
  rw [cons_add_cons, cons_add_cons, empty_add_empty]
#align matrix.vec2_add Matrix.vec2_add
-/

#print Matrix.vec3_add /-
theorem vec3_add [Add α] (a₀ a₁ a₂ b₀ b₁ b₂ : α) :
    ![a₀, a₁, a₂] + ![b₀, b₁, b₂] = ![a₀ + b₀, a₁ + b₁, a₂ + b₂] := by
  rw [cons_add_cons, cons_add_cons, cons_add_cons, empty_add_empty]
#align matrix.vec3_add Matrix.vec3_add
-/

/- warning: matrix.smul_vec2 -> Matrix.smul_vec2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : SMul.{u2, u1} R α] (x : R) (a₀ : α) (a₁ : α), Eq.{succ u1} ((Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))) -> α) (SMul.smul.{u2, u1} R ((Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))) -> α) (Function.hasSMul.{0, u2, u1} (Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))) R α _inst_1) x (Matrix.vecCons.{u1} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) a₀ (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a₁ (Matrix.vecEmpty.{u1} α)))) (Matrix.vecCons.{u1} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (SMul.smul.{u2, u1} R α _inst_1 x a₀) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (SMul.smul.{u2, u1} R α _inst_1 x a₁) (Matrix.vecEmpty.{u1} α)))
but is expected to have type
  forall {α : Type.{u2}} {R : Type.{u1}} [_inst_1 : SMul.{u1, u2} R α] (x : R) (a₀ : α) (a₁ : α), Eq.{succ u2} ((Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) -> α) (HSMul.hSMul.{u1, u2, u2} R ((Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) -> α) ((Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) -> α) (instHSMul.{u1, u2} R ((Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) -> α) (Pi.instSMul.{0, u2, u1} (Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) R (fun (a._@.Mathlib.Data.Fin.VecNotation._hyg.29 : Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) => α) (fun (i : Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) => _inst_1))) x (Matrix.vecCons.{u2} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) a₀ (Matrix.vecCons.{u2} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a₁ (Matrix.vecEmpty.{u2} α)))) (Matrix.vecCons.{u2} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (HSMul.hSMul.{u1, u2, u2} R α α (instHSMul.{u1, u2} R α _inst_1) x a₀) (Matrix.vecCons.{u2} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (HSMul.hSMul.{u1, u2, u2} R α α (instHSMul.{u1, u2} R α _inst_1) x a₁) (Matrix.vecEmpty.{u2} α)))
Case conversion may be inaccurate. Consider using '#align matrix.smul_vec2 Matrix.smul_vec2ₓ'. -/
theorem smul_vec2 {R : Type _} [SMul R α] (x : R) (a₀ a₁ : α) : x • ![a₀, a₁] = ![x • a₀, x • a₁] :=
  by rw [smul_cons, smul_cons, smul_empty]
#align matrix.smul_vec2 Matrix.smul_vec2

/- warning: matrix.smul_vec3 -> Matrix.smul_vec3 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : SMul.{u2, u1} R α] (x : R) (a₀ : α) (a₁ : α) (a₂ : α), Eq.{succ u1} ((Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))))) -> α) (SMul.smul.{u2, u1} R ((Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))))) -> α) (Function.hasSMul.{0, u2, u1} (Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))))) R α _inst_1) x (Matrix.vecCons.{u1} α (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) a₀ (Matrix.vecCons.{u1} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) a₁ (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a₂ (Matrix.vecEmpty.{u1} α))))) (Matrix.vecCons.{u1} α (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) (SMul.smul.{u2, u1} R α _inst_1 x a₀) (Matrix.vecCons.{u1} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (SMul.smul.{u2, u1} R α _inst_1 x a₁) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (SMul.smul.{u2, u1} R α _inst_1 x a₂) (Matrix.vecEmpty.{u1} α))))
but is expected to have type
  forall {α : Type.{u2}} {R : Type.{u1}} [_inst_1 : SMul.{u1, u2} R α] (x : R) (a₀ : α) (a₁ : α) (a₂ : α), Eq.{succ u2} ((Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) -> α) (HSMul.hSMul.{u1, u2, u2} R ((Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) -> α) ((Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) -> α) (instHSMul.{u1, u2} R ((Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) -> α) (Pi.instSMul.{0, u2, u1} (Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) R (fun (a._@.Mathlib.Data.Fin.VecNotation._hyg.29 : Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) => α) (fun (i : Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) => _inst_1))) x (Matrix.vecCons.{u2} α (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) a₀ (Matrix.vecCons.{u2} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) a₁ (Matrix.vecCons.{u2} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a₂ (Matrix.vecEmpty.{u2} α))))) (Matrix.vecCons.{u2} α (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) (HSMul.hSMul.{u1, u2, u2} R α α (instHSMul.{u1, u2} R α _inst_1) x a₀) (Matrix.vecCons.{u2} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (HSMul.hSMul.{u1, u2, u2} R α α (instHSMul.{u1, u2} R α _inst_1) x a₁) (Matrix.vecCons.{u2} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (HSMul.hSMul.{u1, u2, u2} R α α (instHSMul.{u1, u2} R α _inst_1) x a₂) (Matrix.vecEmpty.{u2} α))))
Case conversion may be inaccurate. Consider using '#align matrix.smul_vec3 Matrix.smul_vec3ₓ'. -/
theorem smul_vec3 {R : Type _} [SMul R α] (x : R) (a₀ a₁ a₂ : α) :
    x • ![a₀, a₁, a₂] = ![x • a₀, x • a₁, x • a₂] := by
  rw [smul_cons, smul_cons, smul_cons, smul_empty]
#align matrix.smul_vec3 Matrix.smul_vec3

variable [AddCommMonoid α] [Mul α]

/- warning: matrix.vec2_dot_product' -> Matrix.vec2_dot_product' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] {a₀ : α} {a₁ : α} {b₀ : α} {b₁ : α}, Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))) α (Fin.fintype (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))) _inst_2 _inst_1 (Matrix.vecCons.{u1} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) a₀ (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a₁ (Matrix.vecEmpty.{u1} α))) (Matrix.vecCons.{u1} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) b₀ (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) b₁ (Matrix.vecEmpty.{u1} α)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a₀ b₀) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a₁ b₁))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] {a₀ : α} {a₁ : α} {b₀ : α} {b₁ : α}, Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) α (Fin.fintype (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) _inst_2 _inst_1 (Matrix.vecCons.{u1} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) a₀ (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a₁ (Matrix.vecEmpty.{u1} α))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b₀ (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) b₁ (Matrix.vecEmpty.{u1} α)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a₀ b₀) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a₁ b₁))
Case conversion may be inaccurate. Consider using '#align matrix.vec2_dot_product' Matrix.vec2_dot_product'ₓ'. -/
theorem vec2_dot_product' {a₀ a₁ b₀ b₁ : α} : ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁ := by
  rw [cons_dot_product_cons, cons_dot_product_cons, dot_product_empty, add_zero]
#align matrix.vec2_dot_product' Matrix.vec2_dot_product'

/- warning: matrix.vec2_dot_product -> Matrix.vec2_dotProduct is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (v : (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (w : (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2 _inst_1 v w) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (v (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (w (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (v (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (w (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (v : (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α) (w : (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) α (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2 _inst_1 v w) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (v (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (w (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (v (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (w (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))))
Case conversion may be inaccurate. Consider using '#align matrix.vec2_dot_product Matrix.vec2_dotProductₓ'. -/
@[simp]
theorem vec2_dotProduct (v w : Fin 2 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 :=
  vec2_dot_product'
#align matrix.vec2_dot_product Matrix.vec2_dotProduct

/- warning: matrix.vec3_dot_product' -> Matrix.vec3_dot_product' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] {a₀ : α} {a₁ : α} {a₂ : α} {b₀ : α} {b₁ : α} {b₂ : α}, Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))))) α (Fin.fintype (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))))) _inst_2 _inst_1 (Matrix.vecCons.{u1} α (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) a₀ (Matrix.vecCons.{u1} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) a₁ (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a₂ (Matrix.vecEmpty.{u1} α)))) (Matrix.vecCons.{u1} α (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) b₀ (Matrix.vecCons.{u1} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) b₁ (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) b₂ (Matrix.vecEmpty.{u1} α))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a₀ b₀) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a₁ b₁)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a₂ b₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] {a₀ : α} {a₁ : α} {a₂ : α} {b₀ : α} {b₁ : α} {b₂ : α}, Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) α (Fin.fintype (Nat.succ (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) _inst_2 _inst_1 (Matrix.vecCons.{u1} α (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) a₀ (Matrix.vecCons.{u1} α (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) a₁ (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a₂ (Matrix.vecEmpty.{u1} α)))) (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) b₀ (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b₁ (Matrix.vecCons.{u1} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) b₂ (Matrix.vecEmpty.{u1} α))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a₀ b₀) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a₁ b₁)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a₂ b₂))
Case conversion may be inaccurate. Consider using '#align matrix.vec3_dot_product' Matrix.vec3_dot_product'ₓ'. -/
theorem vec3_dot_product' {a₀ a₁ a₂ b₀ b₁ b₂ : α} :
    ![a₀, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] = a₀ * b₀ + a₁ * b₁ + a₂ * b₂ := by
  rw [cons_dot_product_cons, cons_dot_product_cons, cons_dot_product_cons, dot_product_empty,
    add_zero, add_assoc]
#align matrix.vec3_dot_product' Matrix.vec3_dot_product'

/- warning: matrix.vec3_dot_product -> Matrix.vec3_dotProduct is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (v : (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (w : (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) α (Fin.fintype (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2 _inst_1 v w) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (v (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))))))) (w (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring))))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (v (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))))))) (w (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (v (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 2 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 2 (bit0.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring))))))))) (w (OfNat.ofNat.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 2 (OfNat.mk.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 2 (bit0.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (One.one.{0} (Fin (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.three.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] (v : (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> α) (w : (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) α (Fin.fintype (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) _inst_2 _inst_1 v w) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (v (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (w (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (v (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (w (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (v (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 2 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 2 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (w (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 2 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) 2 (NeZero.succ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))))
Case conversion may be inaccurate. Consider using '#align matrix.vec3_dot_product Matrix.vec3_dotProductₓ'. -/
@[simp]
theorem vec3_dotProduct (v w : Fin 3 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
  vec3_dot_product'
#align matrix.vec3_dot_product Matrix.vec3_dotProduct

end Vec2AndVec3

end Matrix

