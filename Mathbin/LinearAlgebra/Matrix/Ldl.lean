/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp

! This file was ported from Lean 3 source module linear_algebra.matrix.ldl
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathbin.LinearAlgebra.Matrix.PosDef

/-! # LDL decomposition

This file proves the LDL-decomposition of matricies: Any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix.

## Main definitions

 * `LDL.lower` is the lower triangular matrix `L`.
 * `LDL.lower_inv` is the inverse of the lower triangular matrix `L`.
 * `LDL.diag` is the diagonal matrix `D`.

## Main result

* `ldl_decomposition` states that any positive definite matrix can be decomposed as `LDLᴴ`.

## TODO

* Prove that `LDL.lower` is lower triangular from `LDL.lower_inv_triangular`.

-/


variable {𝕜 : Type _} [IsROrC 𝕜]

variable {n : Type _} [LinearOrder n] [IsWellOrder n (· < ·)] [LocallyFiniteOrderBot n]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" =>
  @inner 𝕜 (n → 𝕜) (PiLp.innerProductSpace fun _ => 𝕜).toHasInner x y

open Matrix

open Matrix

variable {S : Matrix n n 𝕜} [Fintype n] (hS : S.PosDef)

/-- The inverse of the lower triangular matrix `L` of the LDL-decomposition. It is obtained by
applying Gram-Schmidt-Orthogonalization w.r.t. the inner product induced by `Sᵀ` on the standard
basis vectors `pi.basis_fun`. -/
noncomputable def LDL.lowerInv : Matrix n n 𝕜 :=
  @gramSchmidt 𝕜 (n → 𝕜) _ (InnerProductSpace.ofMatrix hS.transpose) n _ _ _ fun k =>
    Pi.basisFun 𝕜 n k
#align LDL.lower_inv LDL.lowerInv

theorem LDL.lower_inv_eq_gram_schmidt_basis :
    LDL.lowerInv hS =
      ((Pi.basisFun 𝕜 n).toMatrix
          (@gramSchmidtBasis 𝕜 (n → 𝕜) _ (InnerProductSpace.ofMatrix hS.transpose) n _ _ _
            (Pi.basisFun 𝕜 n)))ᵀ :=
  by
  ext (i j)
  rw [LDL.lowerInv, Basis.CoePiBasisFun.to_matrix_eq_transpose, coe_gram_schmidt_basis]
  rfl
#align LDL.lower_inv_eq_gram_schmidt_basis LDL.lower_inv_eq_gram_schmidt_basis

noncomputable instance LDL.invertibleLowerInv : Invertible (LDL.lowerInv hS) :=
  by
  rw [LDL.lower_inv_eq_gram_schmidt_basis]
  haveI :=
    Basis.invertibleToMatrix (Pi.basisFun 𝕜 n)
      (@gramSchmidtBasis 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose) n _ _ _
        (Pi.basisFun 𝕜 n))
  infer_instance
#align LDL.invertible_lower_inv LDL.invertibleLowerInv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `LDL.lower_inv_orthogonal [])
      (Command.declSig
       [(Term.implicitBinder "{" [`i `j] [":" `n] "}")
        (Term.explicitBinder "(" [`h₀] [":" («term_≠_» `i "≠" `j)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (LinearAlgebra.Matrix.Ldl.«term⟪_,_⟫»
          "⟪"
          (Term.app `LDL.lowerInv [`hS `i])
          ", "
          (Term.app
           (Term.proj (Matrix.Data.Matrix.Basic.matrix.transpose `S "ᵀ") "." `mulVec)
           [(Term.app `LDL.lowerInv [`hS `j])])
          "⟫")
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        («term_=_»
         (Term.app
          (Term.explicit "@" `inner)
          [`𝕜
           (Term.arrow `n "→" `𝕜)
           (Term.proj
            (Term.app `InnerProductSpace.ofMatrix [(Term.proj `hS "." `transpose)])
            "."
            `toHasInner)
           (Term.app `LDL.lowerInv [`hS `i])
           (Term.app `LDL.lowerInv [`hS `j])])
         "="
         (num "0"))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.apply
             "apply"
             (Term.app `gram_schmidt_orthogonal [(Term.hole "_") (Term.hole "_") `h₀]))]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.app
         (Term.explicit "@" `inner)
         [`𝕜
          (Term.arrow `n "→" `𝕜)
          (Term.proj
           (Term.app `InnerProductSpace.ofMatrix [(Term.proj `hS "." `transpose)])
           "."
           `toHasInner)
          (Term.app `LDL.lowerInv [`hS `i])
          (Term.app `LDL.lowerInv [`hS `j])])
        "="
        (num "0"))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.app `gram_schmidt_orthogonal [(Term.hole "_") (Term.hole "_") `h₀]))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app `gram_schmidt_orthogonal [(Term.hole "_") (Term.hole "_") `h₀]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `gram_schmidt_orthogonal [(Term.hole "_") (Term.hole "_") `h₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gram_schmidt_orthogonal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.explicit "@" `inner)
        [`𝕜
         (Term.arrow `n "→" `𝕜)
         (Term.proj
          (Term.app `InnerProductSpace.ofMatrix [(Term.proj `hS "." `transpose)])
          "."
          `toHasInner)
         (Term.app `LDL.lowerInv [`hS `i])
         (Term.app `LDL.lowerInv [`hS `j])])
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.explicit "@" `inner)
       [`𝕜
        (Term.arrow `n "→" `𝕜)
        (Term.proj
         (Term.app `InnerProductSpace.ofMatrix [(Term.proj `hS "." `transpose)])
         "."
         `toHasInner)
        (Term.app `LDL.lowerInv [`hS `i])
        (Term.app `LDL.lowerInv [`hS `j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LDL.lowerInv [`hS `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hS
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LDL.lowerInv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `LDL.lowerInv [`hS `j]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `LDL.lowerInv [`hS `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hS
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LDL.lowerInv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `LDL.lowerInv [`hS `i]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app `InnerProductSpace.ofMatrix [(Term.proj `hS "." `transpose)])
       "."
       `toHasInner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `InnerProductSpace.ofMatrix [(Term.proj `hS "." `transpose)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hS "." `transpose)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hS
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `InnerProductSpace.ofMatrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `InnerProductSpace.ofMatrix [(Term.proj `hS "." `transpose)])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.arrow `n "→" `𝕜)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 25, (some 25, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.arrow `n "→" `𝕜) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `inner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (LinearAlgebra.Matrix.Ldl.«term⟪_,_⟫»
        "⟪"
        (Term.app `LDL.lowerInv [`hS `i])
        ", "
        (Term.app
         (Term.proj (Matrix.Data.Matrix.Basic.matrix.transpose `S "ᵀ") "." `mulVec)
         [(Term.app `LDL.lowerInv [`hS `j])])
        "⟫")
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (LinearAlgebra.Matrix.Ldl.«term⟪_,_⟫»
       "⟪"
       (Term.app `LDL.lowerInv [`hS `i])
       ", "
       (Term.app
        (Term.proj (Matrix.Data.Matrix.Basic.matrix.transpose `S "ᵀ") "." `mulVec)
        [(Term.app `LDL.lowerInv [`hS `j])])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.Matrix.Ldl.«term⟪_,_⟫»', expected 'LinearAlgebra.Matrix.Ldl.term⟪_,_⟫._@.LinearAlgebra.Matrix.Ldl._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  LDL.lower_inv_orthogonal
  { i j : n } ( h₀ : i ≠ j ) : ⟪ LDL.lowerInv hS i , S ᵀ . mulVec LDL.lowerInv hS j ⟫ = 0
  :=
    show
      @ inner
          𝕜
            n → 𝕜
            InnerProductSpace.ofMatrix hS . transpose . toHasInner
            LDL.lowerInv hS i
            LDL.lowerInv hS j
        =
        0
      by apply gram_schmidt_orthogonal _ _ h₀
#align LDL.lower_inv_orthogonal LDL.lower_inv_orthogonal

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The entries of the diagonal matrix `D` of the LDL decomposition. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `LDL.diagEntries [])
      (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `n "→" `𝕜))])
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`i]
         []
         "=>"
         (LinearAlgebra.Matrix.Ldl.«term⟪_,_⟫»
          "⟪"
          (Term.app `star [(Term.app `LDL.lowerInv [`hS `i])])
          ", "
          (Term.app
           (Term.proj `S "." `mulVec)
           [(Term.app `star [(Term.app `LDL.lowerInv [`hS `i])])])
          "⟫")))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        (LinearAlgebra.Matrix.Ldl.«term⟪_,_⟫»
         "⟪"
         (Term.app `star [(Term.app `LDL.lowerInv [`hS `i])])
         ", "
         (Term.app
          (Term.proj `S "." `mulVec)
          [(Term.app `star [(Term.app `LDL.lowerInv [`hS `i])])])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LinearAlgebra.Matrix.Ldl.«term⟪_,_⟫»
       "⟪"
       (Term.app `star [(Term.app `LDL.lowerInv [`hS `i])])
       ", "
       (Term.app (Term.proj `S "." `mulVec) [(Term.app `star [(Term.app `LDL.lowerInv [`hS `i])])])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.Matrix.Ldl.«term⟪_,_⟫»', expected 'LinearAlgebra.Matrix.Ldl.term⟪_,_⟫._@.LinearAlgebra.Matrix.Ldl._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The entries of the diagonal matrix `D` of the LDL decomposition. -/ noncomputable
  def
    LDL.diagEntries
    : n → 𝕜
    := fun i => ⟪ star LDL.lowerInv hS i , S . mulVec star LDL.lowerInv hS i ⟫
#align LDL.diag_entries LDL.diagEntries

/-- The diagonal matrix `D` of the LDL decomposition. -/
noncomputable def LDL.diag : Matrix n n 𝕜 :=
  Matrix.diagonal (LDL.diagEntries hS)
#align LDL.diag LDL.diag

theorem LDL.lower_inv_triangular {i j : n} (hij : i < j) : LDL.lowerInv hS i j = 0 := by
  rw [←
    @gram_schmidt_triangular 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose) n _ _ _ i j
      hij (Pi.basisFun 𝕜 n),
    Pi.basis_fun_repr, LDL.lowerInv]
#align LDL.lower_inv_triangular LDL.lower_inv_triangular

/-- Inverse statement of **LDL decomposition**: we can conjugate a positive definite matrix
by some lower triangular matrix and get a diagonal matrix. -/
theorem LDL.diag_eq_lower_inv_conj : LDL.diag hS = LDL.lowerInv hS ⬝ S ⬝ (LDL.lowerInv hS)ᴴ :=
  by
  ext (i j)
  by_cases hij : i = j
  ·
    simpa only [hij, LDL.diag, diagonal_apply_eq, LDL.diagEntries, Matrix.mul_assoc, inner,
      Pi.star_apply, IsROrC.star_def, star_ring_end_self_apply]
  · simp only [LDL.diag, hij, diagonal_apply_ne, Ne.def, not_false_iff, mul_mul_apply]
    rw [conj_transpose, transpose_map, transpose_transpose, dot_product_mul_vec,
      (LDL.lower_inv_orthogonal hS fun h : j = i => hij h.symm).symm, ← inner_conj_sym,
      mul_vec_transpose, EuclideanSpace.inner_eq_star_dot_product, ← IsROrC.star_def, ←
      star_dot_product_star, dot_product_comm, star_star]
    rfl
#align LDL.diag_eq_lower_inv_conj LDL.diag_eq_lower_inv_conj

/-- The lower triangular matrix `L` of the LDL decomposition. -/
noncomputable def LDL.lower :=
  (LDL.lowerInv hS)⁻¹
#align LDL.lower LDL.lower

/-- **LDL decomposition**: any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix.  -/
theorem LDL.lower_conj_diag : LDL.lower hS ⬝ LDL.diag hS ⬝ (LDL.lower hS)ᴴ = S :=
  by
  rw [LDL.lower, conj_transpose_nonsing_inv, Matrix.mul_assoc,
    Matrix.inv_mul_eq_iff_eq_mul_of_invertible (LDL.lowerInv hS),
    Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  exact LDL.diag_eq_lower_inv_conj hS
#align LDL.lower_conj_diag LDL.lower_conj_diag

