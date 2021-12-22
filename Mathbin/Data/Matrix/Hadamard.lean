import Mathbin.LinearAlgebra.Matrix.Trace

/-!
# Hadamard product of matrices

This file defines the Hadamard product `matrix.hadamard`
and contains basic properties about them.

## Main definition

- `matrix.hadamard`: defines the Hadamard product,
  which is the pointwise product of two matrices of the same size.

## Notation

* `⊙`: the Hadamard product `matrix.hadamard`;

## References

*  <https://en.wikipedia.org/wiki/hadamard_product_(matrices)>

## Tags

hadamard product, hadamard
-/


variable {α β γ m n : Type _}

variable {R : Type _}

namespace Matrix

open_locale Matrix BigOperators

/--  `matrix.hadamard` defines the Hadamard product,
    which is the pointwise product of two matrices of the same size.-/
@[simp]
def hadamard [Mul α] (A : Matrix m n α) (B : Matrix m n α) : Matrix m n α
  | i, j => A i j*B i j

localized [Matrix] infixl:100 " ⊙ " => Matrix.hadamard

section BasicProperties

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

theorem hadamard_comm [CommSemigroupₓ α] : A ⊙ B = B ⊙ A :=
  ext $ fun _ _ => mul_commₓ _ _

theorem hadamard_assoc [Semigroupₓ α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
  ext $ fun _ _ => mul_assocₓ _ _ _

theorem hadamard_add [Distrib α] : (A ⊙ B+C) = (A ⊙ B)+A ⊙ C :=
  ext $ fun _ _ => left_distrib _ _ _

theorem add_hadamard [Distrib α] : (B+C) ⊙ A = (B ⊙ A)+C ⊙ A :=
  ext $ fun _ _ => right_distrib _ _ _

section Scalar

@[simp]
theorem smul_hadamard [Mul α] [HasScalar R α] [IsScalarTower R α α] (k : R) : (k • A) ⊙ B = k • A ⊙ B :=
  ext $ fun _ _ => smul_mul_assoc _ _ _

@[simp]
theorem hadamard_smul [Mul α] [HasScalar R α] [SmulCommClass R α α] (k : R) : A ⊙ (k • B) = k • A ⊙ B :=
  ext $ fun _ _ => mul_smul_comm _ _ _

end Scalar

section Zero

variable [MulZeroClass α]

@[simp]
theorem hadamard_zero : A ⊙ (0 : Matrix m n α) = 0 :=
  ext $ fun _ _ => mul_zero _

@[simp]
theorem zero_hadamard : (0 : Matrix m n α) ⊙ A = 0 :=
  ext $ fun _ _ => zero_mul _

end Zero

section One

variable [DecidableEq n] [MulZeroOneClass α]

variable (M : Matrix n n α)

theorem hadamard_one : M ⊙ (1 : Matrix n n α) = diagonal fun i => M i i := by
  ext
  by_cases' h : i = j <;> simp [h]

theorem one_hadamard : (1 : Matrix n n α) ⊙ M = diagonal fun i => M i i := by
  ext
  by_cases' h : i = j <;> simp [h]

end One

section Diagonal

variable [DecidableEq n] [MulZeroClass α]

theorem diagonal_hadamard_diagonal (v : n → α) (w : n → α) : diagonal v ⊙ diagonal w = diagonal (v*w) :=
  ext $ fun _ _ => (apply_ite2 _ _ _ _ _ _).trans (congr_argₓ _ $ zero_mul 0)

end Diagonal

section trace

variable [Fintype m] [Fintype n]

variable (R) [Semiringₓ α] [Semiringₓ R] [Module R α]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_hadamard_eq [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" `m ")")
        (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `j)] ":" `n ")")])
      ", "
      (Term.app (Matrix.Data.Matrix.Hadamard.«term_⊙_» `A " ⊙ " `B) [`i `j]))
     "="
     (Term.app
      `trace
      [`m `R `α (Matrix.Data.Matrix.Basic.«term_⬝_» `A " ⬝ " (Matrix.Data.Matrix.Basic.«term_ᵀ» `B "ᵀ"))]))))
  (Command.declValSimple ":=" `rfl [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" `m ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `j)] ":" `n ")")])
    ", "
    (Term.app (Matrix.Data.Matrix.Hadamard.«term_⊙_» `A " ⊙ " `B) [`i `j]))
   "="
   (Term.app
    `trace
    [`m `R `α (Matrix.Data.Matrix.Basic.«term_⬝_» `A " ⬝ " (Matrix.Data.Matrix.Basic.«term_ᵀ» `B "ᵀ"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `trace [`m `R `α (Matrix.Data.Matrix.Basic.«term_⬝_» `A " ⬝ " (Matrix.Data.Matrix.Basic.«term_ᵀ» `B "ᵀ"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Matrix.Basic.«term_⬝_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Matrix.Basic.«term_⬝_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Matrix.Basic.«term_⬝_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Matrix.Basic.«term_⬝_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Matrix.Basic.«term_⬝_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Matrix.Data.Matrix.Basic.«term_⬝_» `A " ⬝ " (Matrix.Data.Matrix.Basic.«term_ᵀ» `B "ᵀ"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Matrix.Basic.«term_⬝_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Matrix.Data.Matrix.Basic.«term_ᵀ» `B "ᵀ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Matrix.Basic.«term_ᵀ»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1500, term))
  `B
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1500 >? 1024, (none, [anonymous]) <=? (some 1500, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [`B []] ")")
[PrettyPrinter.parenthesize] ...precedences are 76 >? 1500, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 76, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Matrix.Data.Matrix.Basic.«term_⬝_» `A " ⬝ " (Matrix.Data.Matrix.Basic.«term_ᵀ» (Term.paren "(" [`B []] ")") "ᵀ")) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `trace
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" `m ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `j)] ":" `n ")")])
   ", "
   (Term.app (Matrix.Data.Matrix.Hadamard.«term_⊙_» `A " ⊙ " `B) [`i `j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Matrix.Data.Matrix.Hadamard.«term_⊙_» `A " ⊙ " `B) [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Matrix.Data.Matrix.Hadamard.«term_⊙_» `A " ⊙ " `B)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Matrix.Hadamard.«term_⊙_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `B
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 100, (some 101, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Matrix.Data.Matrix.Hadamard.«term_⊙_» `A " ⊙ " `B) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem sum_hadamard_eq : ∑ ( i : m ) ( j : n ) , A ⊙ B i j = trace m R α A ⬝ B ᵀ := rfl

theorem dot_product_vec_mul_hadamard [DecidableEq m] [DecidableEq n] (v : m → α) (w : n → α) :
    dot_product (vec_mul v (A ⊙ B)) w = trace m R α (diagonal v ⬝ A ⬝ (B ⬝ diagonal w)ᵀ) := by
  rw [← sum_hadamard_eq, Finset.sum_comm]
  simp [dot_product, vec_mul, Finset.sum_mul, mul_assocₓ]

end trace

end BasicProperties

end Matrix

