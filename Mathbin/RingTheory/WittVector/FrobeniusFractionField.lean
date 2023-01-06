/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth

! This file was ported from Lean 3 source module ring_theory.witt_vector.frobenius_fraction_field
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Cast.WithTop
import Mathbin.FieldTheory.IsAlgClosed.Basic
import Mathbin.RingTheory.WittVector.DiscreteValuationRing

/-!
# Solving equations about the Frobenius map on the field of fractions of `𝕎 k`

The goal of this file is to prove `witt_vector.exists_frobenius_solution_fraction_ring`,
which says that for an algebraically closed field `k` of characteristic `p` and `a, b` in the
field of fractions of Witt vectors over `k`,
there is a solution `b` to the equation `φ b * a = p ^ m * b`, where `φ` is the Frobenius map.

Most of this file builds up the equivalent theorem over `𝕎 k` directly,
moving to the field of fractions at the end.
See `witt_vector.frobenius_rotation` and its specification.

The construction proceeds by recursively defining a sequence of coefficients as solutions to a
polynomial equation in `k`. We must define these as generic polynomials using Witt vector API
(`witt_vector.witt_mul`, `witt_polynomial`) to show that they satisfy the desired equation.

Preliminary work is done in the dependency `ring_theory.witt_vector.mul_coeff`
to isolate the `n+1`st coefficients of `x` and `y` in the `n+1`st coefficient of `x*y`.

This construction is described in Dupuis, Lewis, and Macbeth,
[Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022].
We approximately follow an approach sketched on MathOverflow:
<https://mathoverflow.net/questions/62468/about-frobenius-of-witt-vectors>

The result is a dependency for the proof of `witt_vector.isocrystal_classification`,
the classification of one-dimensional isocrystals over an algebraically closed field.
-/


noncomputable section

namespace WittVector

variable (p : ℕ) [hp : Fact p.Prime]

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p

namespace RecursionMain

/-!

## The recursive case of the vector coefficients

The first coefficient of our solution vector is easy to define below.
In this section we focus on the recursive case.
The goal is to turn `witt_poly_prod n` into a univariate polynomial
whose variable represents the `n`th coefficient of `x` in `x * a`.

-/


section CommRing

include hp

variable {k : Type _} [CommRing k] [CharP k p]

open Polynomial

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The root of this polynomial determines the `n+1`st coefficient of our solution. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `succNthDefiningPoly [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`bs]
         [":" (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `Polynomial [`k]))])
      (Command.declValSimple
       ":="
       («term_+_»
        («term_-_»
         («term_*_»
          («term_^_» `X "^" `p)
          "*"
          (Term.app
           `c
           [(«term_^_»
             (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
         "-"
         («term_*_»
          `X
          "*"
          (Term.app
           `c
           [(«term_^_»
             (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])))
        "+"
        (Term.app
         `c
         [(«term_-_»
           («term_-_»
            («term_+_»
             («term_*_»
              (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
              "*"
              («term_^_»
               («term_^_» (Term.app `bs [(num "0")]) "^" `p)
               "^"
               («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
             "+"
             (Term.app
              `nthRemainder
              [`p
               `n
               (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
               (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])]))
            "-"
            («term_*_»
             (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
             "*"
             («term_^_»
              (Term.app `bs [(num "0")])
              "^"
              («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
           "-"
           (Term.app
            `nthRemainder
            [`p `n `bs (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₂])]))]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_-_»
        («term_*_»
         («term_^_» `X "^" `p)
         "*"
         (Term.app
          `c
          [(«term_^_»
            (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
            "^"
            («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
        "-"
        («term_*_»
         `X
         "*"
         (Term.app
          `c
          [(«term_^_»
            (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
            "^"
            («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])))
       "+"
       (Term.app
        `c
        [(«term_-_»
          («term_-_»
           («term_+_»
            («term_*_»
             (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
             "*"
             («term_^_»
              («term_^_» (Term.app `bs [(num "0")]) "^" `p)
              "^"
              («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
            "+"
            (Term.app
             `nthRemainder
             [`p
              `n
              (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
              (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])]))
           "-"
           («term_*_»
            (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "*"
            («term_^_»
             (Term.app `bs [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
          "-"
          (Term.app
           `nthRemainder
           [`p `n `bs (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₂])]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `c
       [(«term_-_»
         («term_-_»
          («term_+_»
           («term_*_»
            (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "*"
            («term_^_»
             («term_^_» (Term.app `bs [(num "0")]) "^" `p)
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
           "+"
           (Term.app
            `nthRemainder
            [`p
             `n
             (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
             (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])]))
          "-"
          («term_*_»
           (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
           "*"
           («term_^_»
            (Term.app `bs [(num "0")])
            "^"
            («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
         "-"
         (Term.app
          `nthRemainder
          [`p `n `bs (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₂])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       («term_-_»
        («term_+_»
         («term_*_»
          (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "*"
          («term_^_»
           («term_^_» (Term.app `bs [(num "0")]) "^" `p)
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
         "+"
         (Term.app
          `nthRemainder
          [`p
           `n
           (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
           (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])]))
        "-"
        («term_*_»
         (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         («term_^_»
          (Term.app `bs [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
       "-"
       (Term.app
        `nthRemainder
        [`p `n `bs (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₂])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nthRemainder
       [`p `n `bs (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `truncateFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `a₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nthRemainder
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_-_»
       («term_+_»
        («term_*_»
         (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         («term_^_»
          («term_^_» (Term.app `bs [(num "0")]) "^" `p)
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
        "+"
        (Term.app
         `nthRemainder
         [`p
          `n
          (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
          (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])]))
       "-"
       («term_*_»
        (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        («term_^_» (Term.app `bs [(num "0")]) "^" («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       («term_^_» (Term.app `bs [(num "0")]) "^" («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `bs [(num "0")]) "^" («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `bs [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       («term_*_»
        (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        («term_^_»
         («term_^_» (Term.app `bs [(num "0")]) "^" `p)
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
       "+"
       (Term.app
        `nthRemainder
        [`p
         `n
         (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
         (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nthRemainder
       [`p
        `n
        (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
        (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `truncateFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `a₁])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `bs [`v]) "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `bs [`v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nthRemainder
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       («term_^_»
        («term_^_» (Term.app `bs [(num "0")]) "^" `p)
        "^"
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       («term_^_» (Term.app `bs [(num "0")]) "^" `p)
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_^_» (Term.app `bs [(num "0")]) "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `bs [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 80, (some 80, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_» (Term.app `bs [(num "0")]) "^" `p)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_»
      («term_-_»
       («term_+_»
        («term_*_»
         (Term.app (Term.proj `a₁ "." `coeff) [(Term.paren "(" («term_+_» `n "+" (num "1")) ")")])
         "*"
         («term_^_»
          (Term.paren "(" («term_^_» (Term.app `bs [(num "0")]) "^" `p) ")")
          "^"
          («term_^_» `p "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")"))))
        "+"
        (Term.app
         `nthRemainder
         [`p
          `n
          (Term.paren
           "("
           (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
           ")")
          (Term.paren
           "("
           (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `a₁])
           ")")]))
       "-"
       («term_*_»
        (Term.app (Term.proj `a₂ "." `coeff) [(Term.paren "(" («term_+_» `n "+" (num "1")) ")")])
        "*"
        («term_^_»
         (Term.app `bs [(num "0")])
         "^"
         («term_^_» `p "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")")))))
      "-"
      (Term.app
       `nthRemainder
       [`p
        `n
        `bs
        (Term.paren
         "("
         (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `a₂])
         ")")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_-_»
       («term_*_»
        («term_^_» `X "^" `p)
        "*"
        (Term.app
         `c
         [(«term_^_»
           (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
       "-"
       («term_*_»
        `X
        "*"
        (Term.app
         `c
         [(«term_^_»
           (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       `X
       "*"
       (Term.app
        `c
        [(«term_^_»
          (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `c
       [(«term_^_»
         (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_»
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
      "^"
      («term_^_» `p "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       («term_^_» `X "^" `p)
       "*"
       (Term.app
        `c
        [(«term_^_»
          (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `c
       [(«term_^_»
         (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_»
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
      "^"
      («term_^_» `p "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `X "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Polynomial [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Polynomial
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `Fin [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The root of this polynomial determines the `n+1`st coefficient of our solution. -/
  def
    succNthDefiningPoly
    ( n : ℕ ) ( a₁ a₂ : 𝕎 k ) ( bs : Fin n + 1 → k ) : Polynomial k
    :=
      X ^ p * c a₁ . coeff 0 ^ p ^ n + 1 - X * c a₂ . coeff 0 ^ p ^ n + 1
        +
        c
          a₁ . coeff n + 1 * bs 0 ^ p ^ p ^ n + 1
                +
                nthRemainder p n fun v => bs v ^ p truncateFun n + 1 a₁
              -
              a₂ . coeff n + 1 * bs 0 ^ p ^ n + 1
            -
            nthRemainder p n bs truncateFun n + 1 a₂
#align
  witt_vector.recursion_main.succ_nth_defining_poly WittVector.RecursionMain.succNthDefiningPoly

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `succ_nth_defining_poly_degree [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsDomain [`k]) "]")
        (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`bs]
         [":" (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₁]
         [":" («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₂]
         [":" («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs]) "." `degree)
         "="
         `p)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.proj
                  («term_*_»
                   («term_^_» `X "^" `p)
                   "*"
                   (Term.app
                    `C
                    [(«term_^_»
                      (Term.app `a₁.coeff [(num "0")])
                      "^"
                      («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
                  "."
                  `degree)
                 "="
                 `p))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `degree_mul) "," (Tactic.rwRule [] `degree_C)]
                    "]")
                   [])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `Nat.cast_withBot)
                       ","
                       (Tactic.simpLemma [] [] `add_zero)
                       ","
                       (Tactic.simpLemma [] [] `degree_X)
                       ","
                       (Tactic.simpLemma [] [] `degree_pow)
                       ","
                       (Tactic.simpLemma [] [] `Nat.smul_one_eq_coe)]
                      "]"]
                     [])])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₁]))])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.proj
                  («term_-_»
                   («term_*_»
                    («term_^_» `X "^" `p)
                    "*"
                    (Term.app
                     `C
                     [(«term_^_»
                       (Term.app `a₁.coeff [(num "0")])
                       "^"
                       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
                   "-"
                   («term_*_»
                    `X
                    "*"
                    (Term.app
                     `C
                     [(«term_^_»
                       (Term.app `a₂.coeff [(num "0")])
                       "^"
                       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])))
                  "."
                  `degree)
                 "="
                 `p))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `degree_sub_eq_left_of_degree_lt)
                     ","
                     (Tactic.rwRule [] `this)]
                    "]")
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `this)
                     ","
                     (Tactic.rwRule [] `degree_mul)
                     ","
                     (Tactic.rwRule [] `degree_C)
                     ","
                     (Tactic.rwRule [] `degree_X)
                     ","
                     (Tactic.rwRule [] `add_zero)]
                    "]")
                   [])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.out.one_lt)])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₂]))])]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `succ_nth_defining_poly)
              ","
              (Tactic.rwRule [] `degree_add_eq_left_of_degree_lt)
              ","
              (Tactic.rwRule [] `this)]
             "]")
            [])
           []
           (Tactic.apply "apply" (Term.app `lt_of_le_of_lt [`degree_C_le]))
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
           []
           (Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.out.pos)])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.proj
                 («term_*_»
                  («term_^_» `X "^" `p)
                  "*"
                  (Term.app
                   `C
                   [(«term_^_»
                     (Term.app `a₁.coeff [(num "0")])
                     "^"
                     («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
                 "."
                 `degree)
                "="
                `p))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `degree_mul) "," (Tactic.rwRule [] `degree_C)]
                   "]")
                  [])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `Nat.cast_withBot)
                      ","
                      (Tactic.simpLemma [] [] `add_zero)
                      ","
                      (Tactic.simpLemma [] [] `degree_X)
                      ","
                      (Tactic.simpLemma [] [] `degree_pow)
                      ","
                      (Tactic.simpLemma [] [] `Nat.smul_one_eq_coe)]
                     "]"]
                    [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₁]))])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.proj
                 («term_-_»
                  («term_*_»
                   («term_^_» `X "^" `p)
                   "*"
                   (Term.app
                    `C
                    [(«term_^_»
                      (Term.app `a₁.coeff [(num "0")])
                      "^"
                      («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
                  "-"
                  («term_*_»
                   `X
                   "*"
                   (Term.app
                    `C
                    [(«term_^_»
                      (Term.app `a₂.coeff [(num "0")])
                      "^"
                      («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])))
                 "."
                 `degree)
                "="
                `p))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `degree_sub_eq_left_of_degree_lt)
                    ","
                    (Tactic.rwRule [] `this)]
                   "]")
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `this)
                    ","
                    (Tactic.rwRule [] `degree_mul)
                    ","
                    (Tactic.rwRule [] `degree_C)
                    ","
                    (Tactic.rwRule [] `degree_X)
                    ","
                    (Tactic.rwRule [] `add_zero)]
                   "]")
                  [])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.out.one_lt)])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₂]))])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `succ_nth_defining_poly)
             ","
             (Tactic.rwRule [] `degree_add_eq_left_of_degree_lt)
             ","
             (Tactic.rwRule [] `this)]
            "]")
           [])
          []
          (Tactic.apply "apply" (Term.app `lt_of_le_of_lt [`degree_C_le]))
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
          []
          (Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.out.pos)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.out.pos)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.out.pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `lt_of_le_of_lt [`degree_C_le]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lt_of_le_of_lt [`degree_C_le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `degree_C_le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_of_le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `succ_nth_defining_poly)
         ","
         (Tactic.rwRule [] `degree_add_eq_left_of_degree_lt)
         ","
         (Tactic.rwRule [] `this)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `degree_add_eq_left_of_degree_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `succ_nth_defining_poly
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.proj
             («term_-_»
              («term_*_»
               («term_^_» `X "^" `p)
               "*"
               (Term.app
                `C
                [(«term_^_»
                  (Term.app `a₁.coeff [(num "0")])
                  "^"
                  («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
              "-"
              («term_*_»
               `X
               "*"
               (Term.app
                `C
                [(«term_^_»
                  (Term.app `a₂.coeff [(num "0")])
                  "^"
                  («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])))
             "."
             `degree)
            "="
            `p))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `degree_sub_eq_left_of_degree_lt) "," (Tactic.rwRule [] `this)]
               "]")
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `this)
                ","
                (Tactic.rwRule [] `degree_mul)
                ","
                (Tactic.rwRule [] `degree_C)
                ","
                (Tactic.rwRule [] `degree_X)
                ","
                (Tactic.rwRule [] `add_zero)]
               "]")
              [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.out.one_lt)])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₂]))])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `degree_sub_eq_left_of_degree_lt) "," (Tactic.rwRule [] `this)]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `this)
             ","
             (Tactic.rwRule [] `degree_mul)
             ","
             (Tactic.rwRule [] `degree_C)
             ","
             (Tactic.rwRule [] `degree_X)
             ","
             (Tactic.rwRule [] `add_zero)]
            "]")
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.out.one_lt)])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₂]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₂]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pow_ne_zero [(Term.hole "_") `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.out.one_lt)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hp.out.one_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.out.one_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `this)
         ","
         (Tactic.rwRule [] `degree_mul)
         ","
         (Tactic.rwRule [] `degree_C)
         ","
         (Tactic.rwRule [] `degree_X)
         ","
         (Tactic.rwRule [] `add_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `degree_X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `degree_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `degree_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `degree_sub_eq_left_of_degree_lt) "," (Tactic.rwRule [] `this)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `degree_sub_eq_left_of_degree_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.proj
        («term_-_»
         («term_*_»
          («term_^_» `X "^" `p)
          "*"
          (Term.app
           `C
           [(«term_^_»
             (Term.app `a₁.coeff [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
         "-"
         («term_*_»
          `X
          "*"
          (Term.app
           `C
           [(«term_^_»
             (Term.app `a₂.coeff [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])))
        "."
        `degree)
       "="
       `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj
       («term_-_»
        («term_*_»
         («term_^_» `X "^" `p)
         "*"
         (Term.app
          `C
          [(«term_^_»
            (Term.app `a₁.coeff [(num "0")])
            "^"
            («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
        "-"
        («term_*_»
         `X
         "*"
         (Term.app
          `C
          [(«term_^_»
            (Term.app `a₂.coeff [(num "0")])
            "^"
            («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])))
       "."
       `degree)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_-_»
       («term_*_»
        («term_^_» `X "^" `p)
        "*"
        (Term.app
         `C
         [(«term_^_»
           (Term.app `a₁.coeff [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
       "-"
       («term_*_»
        `X
        "*"
        (Term.app
         `C
         [(«term_^_»
           (Term.app `a₂.coeff [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       `X
       "*"
       (Term.app
        `C
        [(«term_^_»
          (Term.app `a₂.coeff [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `C
       [(«term_^_»
         (Term.app `a₂.coeff [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app `a₂.coeff [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `a₂.coeff [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `a₂.coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_»
      (Term.app `a₂.coeff [(num "0")])
      "^"
      («term_^_» `p "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       («term_^_» `X "^" `p)
       "*"
       (Term.app
        `C
        [(«term_^_»
          (Term.app `a₁.coeff [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `C
       [(«term_^_»
         (Term.app `a₁.coeff [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app `a₁.coeff [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `a₁.coeff [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `a₁.coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_»
      (Term.app `a₁.coeff [(num "0")])
      "^"
      («term_^_» `p "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `X "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_»
      («term_*_»
       («term_^_» `X "^" `p)
       "*"
       (Term.app
        `C
        [(Term.paren
          "("
          («term_^_»
           (Term.app `a₁.coeff [(num "0")])
           "^"
           («term_^_» `p "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")")))
          ")")]))
      "-"
      («term_*_»
       `X
       "*"
       (Term.app
        `C
        [(Term.paren
          "("
          («term_^_»
           (Term.app `a₂.coeff [(num "0")])
           "^"
           («term_^_» `p "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")")))
          ")")])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.proj
             («term_*_»
              («term_^_» `X "^" `p)
              "*"
              (Term.app
               `C
               [(«term_^_»
                 (Term.app `a₁.coeff [(num "0")])
                 "^"
                 («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
             "."
             `degree)
            "="
            `p))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `degree_mul) "," (Tactic.rwRule [] `degree_C)]
               "]")
              [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Nat.cast_withBot)
                  ","
                  (Tactic.simpLemma [] [] `add_zero)
                  ","
                  (Tactic.simpLemma [] [] `degree_X)
                  ","
                  (Tactic.simpLemma [] [] `degree_pow)
                  ","
                  (Tactic.simpLemma [] [] `Nat.smul_one_eq_coe)]
                 "]"]
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₁]))])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `degree_mul) "," (Tactic.rwRule [] `degree_C)]
            "]")
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Nat.cast_withBot)
               ","
               (Tactic.simpLemma [] [] `add_zero)
               ","
               (Tactic.simpLemma [] [] `degree_X)
               ","
               (Tactic.simpLemma [] [] `degree_pow)
               ","
               (Tactic.simpLemma [] [] `Nat.smul_one_eq_coe)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₁]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₁]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `pow_ne_zero [(Term.hole "_") `ha₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pow_ne_zero [(Term.hole "_") `ha₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Nat.cast_withBot)
           ","
           (Tactic.simpLemma [] [] `add_zero)
           ","
           (Tactic.simpLemma [] [] `degree_X)
           ","
           (Tactic.simpLemma [] [] `degree_pow)
           ","
           (Tactic.simpLemma [] [] `Nat.smul_one_eq_coe)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Nat.cast_withBot)
         ","
         (Tactic.simpLemma [] [] `add_zero)
         ","
         (Tactic.simpLemma [] [] `degree_X)
         ","
         (Tactic.simpLemma [] [] `degree_pow)
         ","
         (Tactic.simpLemma [] [] `Nat.smul_one_eq_coe)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.smul_one_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `degree_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `degree_X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_withBot
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `degree_mul) "," (Tactic.rwRule [] `degree_C)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `degree_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `degree_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.proj
        («term_*_»
         («term_^_» `X "^" `p)
         "*"
         (Term.app
          `C
          [(«term_^_»
            (Term.app `a₁.coeff [(num "0")])
            "^"
            («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
        "."
        `degree)
       "="
       `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj
       («term_*_»
        («term_^_» `X "^" `p)
        "*"
        (Term.app
         `C
         [(«term_^_»
           (Term.app `a₁.coeff [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
       "."
       `degree)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_»
       («term_^_» `X "^" `p)
       "*"
       (Term.app
        `C
        [(«term_^_»
          (Term.app `a₁.coeff [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1"))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `C
       [(«term_^_»
         (Term.app `a₁.coeff [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app `a₁.coeff [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `a₁.coeff [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `a₁.coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_»
      (Term.app `a₁.coeff [(num "0")])
      "^"
      («term_^_» `p "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `X "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      («term_^_» `X "^" `p)
      "*"
      (Term.app
       `C
       [(Term.paren
         "("
         («term_^_»
          (Term.app `a₁.coeff [(num "0")])
          "^"
          («term_^_» `p "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")")))
         ")")]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.proj (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs]) "." `degree) "=" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs]) "." `degree)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succNthDefiningPoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `Fin [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  succ_nth_defining_poly_degree
  [ IsDomain k ]
      ( n : ℕ )
      ( a₁ a₂ : 𝕎 k )
      ( bs : Fin n + 1 → k )
      ( ha₁ : a₁ . coeff 0 ≠ 0 )
      ( ha₂ : a₂ . coeff 0 ≠ 0 )
    : succNthDefiningPoly p n a₁ a₂ bs . degree = p
  :=
    by
      have
          : X ^ p * C a₁.coeff 0 ^ p ^ n + 1 . degree = p
            :=
            by
              rw [ degree_mul , degree_C ]
                ·
                  simp
                    only
                    [ Nat.cast_withBot , add_zero , degree_X , degree_pow , Nat.smul_one_eq_coe ]
                · exact pow_ne_zero _ ha₁
        have
          : X ^ p * C a₁.coeff 0 ^ p ^ n + 1 - X * C a₂.coeff 0 ^ p ^ n + 1 . degree = p
            :=
            by
              rw [ degree_sub_eq_left_of_degree_lt , this ]
                rw [ this , degree_mul , degree_C , degree_X , add_zero ]
                · exact_mod_cast hp.out.one_lt
                · exact pow_ne_zero _ ha₂
        rw [ succ_nth_defining_poly , degree_add_eq_left_of_degree_lt , this ]
        apply lt_of_le_of_lt degree_C_le
        rw [ this ]
        exact_mod_cast hp.out.pos
#align
  witt_vector.recursion_main.succ_nth_defining_poly_degree WittVector.RecursionMain.succ_nth_defining_poly_degree

end CommRing

section IsAlgClosed

include hp

variable {k : Type _} [Field k] [CharP k p] [IsAlgClosed k]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `root_exists [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`bs]
         [":" (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₁]
         [":" («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₂]
         [":" («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" `k]))
         ","
         (Term.app
          (Term.proj (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs]) "." `IsRoot)
          [`b]))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app `IsAlgClosed.exists_root [(Term.hole "_")])
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma
                []
                []
                (Term.app `succ_nth_defining_poly_degree [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]))
               ","
               (Tactic.simpLemma [] [] `hp.out.ne_zero)
               ","
               (Tactic.simpLemma [] [] `WithTop.coe_eq_zero)
               ","
               (Tactic.simpLemma [] [] `Ne.def)
               ","
               (Tactic.simpLemma [] [] `not_false_iff)]
              "]"]
             [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `IsAlgClosed.exists_root [(Term.hole "_")])
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma
               []
               []
               (Term.app `succ_nth_defining_poly_degree [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]))
              ","
              (Tactic.simpLemma [] [] `hp.out.ne_zero)
              ","
              (Tactic.simpLemma [] [] `WithTop.coe_eq_zero)
              ","
              (Tactic.simpLemma [] [] `Ne.def)
              ","
              (Tactic.simpLemma [] [] `not_false_iff)]
             "]"]
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma
              []
              []
              (Term.app `succ_nth_defining_poly_degree [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]))
             ","
             (Tactic.simpLemma [] [] `hp.out.ne_zero)
             ","
             (Tactic.simpLemma [] [] `WithTop.coe_eq_zero)
             ","
             (Tactic.simpLemma [] [] `Ne.def)
             ","
             (Tactic.simpLemma [] [] `not_false_iff)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma
          []
          []
          (Term.app `succ_nth_defining_poly_degree [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]))
         ","
         (Tactic.simpLemma [] [] `hp.out.ne_zero)
         ","
         (Tactic.simpLemma [] [] `WithTop.coe_eq_zero)
         ","
         (Tactic.simpLemma [] [] `Ne.def)
         ","
         (Tactic.simpLemma [] [] `not_false_iff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_false_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ne.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WithTop.coe_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.out.ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `succ_nth_defining_poly_degree [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succ_nth_defining_poly_degree
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `IsAlgClosed.exists_root [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsAlgClosed.exists_root
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" `k]))
       ","
       (Term.app (Term.proj (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs]) "." `IsRoot) [`b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs]) "." `IsRoot) [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs]) "." `IsRoot)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succNthDefiningPoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `Fin [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  root_exists
  ( n : ℕ )
      ( a₁ a₂ : 𝕎 k )
      ( bs : Fin n + 1 → k )
      ( ha₁ : a₁ . coeff 0 ≠ 0 )
      ( ha₂ : a₂ . coeff 0 ≠ 0 )
    : ∃ b : k , succNthDefiningPoly p n a₁ a₂ bs . IsRoot b
  :=
    IsAlgClosed.exists_root _
      <|
      by
        simp
          only
          [
            succ_nth_defining_poly_degree p n a₁ a₂ bs ha₁ ha₂
              ,
              hp.out.ne_zero
              ,
              WithTop.coe_eq_zero
              ,
              Ne.def
              ,
              not_false_iff
            ]
#align witt_vector.recursion_main.root_exists WittVector.RecursionMain.root_exists

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This is the `n+1`st coefficient of our solution, projected from `root_exists`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `succNthVal [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`bs]
         [":" (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₁]
         [":" («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₂]
         [":" («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")]
       [(Term.typeSpec ":" `k)])
      (Command.declValSimple
       ":="
       (Term.app `Classical.choose [(Term.app `root_exists [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Classical.choose [(Term.app `root_exists [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `root_exists [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `root_exists
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `root_exists [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Classical.choose
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `Fin [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- This is the `n+1`st coefficient of our solution, projected from `root_exists`. -/
  def
    succNthVal
    ( n : ℕ )
        ( a₁ a₂ : 𝕎 k )
        ( bs : Fin n + 1 → k )
        ( ha₁ : a₁ . coeff 0 ≠ 0 )
        ( ha₂ : a₂ . coeff 0 ≠ 0 )
      : k
    := Classical.choose root_exists p n a₁ a₂ bs ha₁ ha₂
#align witt_vector.recursion_main.succ_nth_val WittVector.RecursionMain.succNthVal

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `succ_nth_val_spec [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`bs]
         [":" (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₁]
         [":" («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₂]
         [":" («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         (Term.proj (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs]) "." `IsRoot)
         [(Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])])))
      (Command.declValSimple
       ":="
       (Term.app `Classical.choose_spec [(Term.app `root_exists [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Classical.choose_spec [(Term.app `root_exists [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `root_exists [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `root_exists
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `root_exists [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Classical.choose_spec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (Term.proj (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs]) "." `IsRoot)
       [(Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succNthVal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs]) "." `IsRoot)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succNthDefiningPoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `succNthDefiningPoly [`p `n `a₁ `a₂ `bs])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `Fin [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  succ_nth_val_spec
  ( n : ℕ )
      ( a₁ a₂ : 𝕎 k )
      ( bs : Fin n + 1 → k )
      ( ha₁ : a₁ . coeff 0 ≠ 0 )
      ( ha₂ : a₂ . coeff 0 ≠ 0 )
    : succNthDefiningPoly p n a₁ a₂ bs . IsRoot succNthVal p n a₁ a₂ bs ha₁ ha₂
  := Classical.choose_spec root_exists p n a₁ a₂ bs ha₁ ha₂
#align witt_vector.recursion_main.succ_nth_val_spec WittVector.RecursionMain.succ_nth_val_spec

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `succ_nth_val_spec' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`bs]
         [":" (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₁]
         [":" («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₂]
         [":" («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          («term_+_»
           («term_*_»
            («term_^_» (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]) "^" `p)
            "*"
            («term_^_»
             (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
           "+"
           («term_*_»
            (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "*"
            («term_^_»
             («term_^_» (Term.app `bs [(num "0")]) "^" `p)
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
          "+"
          (Term.app
           `nthRemainder
           [`p
            `n
            (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
            (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])]))
         "="
         («term_+_»
          («term_+_»
           («term_*_»
            (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
            "*"
            («term_^_»
             (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
           "+"
           («term_*_»
            (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
            "*"
            («term_^_»
             (Term.app `bs [(num "0")])
             "^"
             («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
          "+"
          (Term.app
           `nthRemainder
           [`p `n `bs (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₂])])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_zero)]
             "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app `succ_nth_val_spec [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]))))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Polynomial.map_add)
              ","
              (Tactic.simpLemma [] [] `Polynomial.eval_X)
              ","
              (Tactic.simpLemma [] [] `Polynomial.map_pow)
              ","
              (Tactic.simpLemma [] [] `Polynomial.eval_C)
              ","
              (Tactic.simpLemma [] [] `Polynomial.eval_pow)
              ","
              (Tactic.simpLemma [] [] `succ_nth_defining_poly)
              ","
              (Tactic.simpLemma [] [] `Polynomial.eval_mul)
              ","
              (Tactic.simpLemma [] [] `Polynomial.eval_add)
              ","
              (Tactic.simpLemma [] [] `Polynomial.eval_sub)
              ","
              (Tactic.simpLemma [] [] `Polynomial.map_mul)
              ","
              (Tactic.simpLemma [] [] `Polynomial.map_sub)
              ","
              (Tactic.simpLemma [] [] `Polynomial.IsRoot.def)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (convert "convert" [] `this ["using" (num "1")])
           []
           (Mathlib.Tactic.RingNF.ring "ring")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_zero)]
            "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app `succ_nth_val_spec [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Polynomial.map_add)
             ","
             (Tactic.simpLemma [] [] `Polynomial.eval_X)
             ","
             (Tactic.simpLemma [] [] `Polynomial.map_pow)
             ","
             (Tactic.simpLemma [] [] `Polynomial.eval_C)
             ","
             (Tactic.simpLemma [] [] `Polynomial.eval_pow)
             ","
             (Tactic.simpLemma [] [] `succ_nth_defining_poly)
             ","
             (Tactic.simpLemma [] [] `Polynomial.eval_mul)
             ","
             (Tactic.simpLemma [] [] `Polynomial.eval_add)
             ","
             (Tactic.simpLemma [] [] `Polynomial.eval_sub)
             ","
             (Tactic.simpLemma [] [] `Polynomial.map_mul)
             ","
             (Tactic.simpLemma [] [] `Polynomial.map_sub)
             ","
             (Tactic.simpLemma [] [] `Polynomial.IsRoot.def)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (convert "convert" [] `this ["using" (num "1")])
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `this ["using" (num "1")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Polynomial.map_add)
         ","
         (Tactic.simpLemma [] [] `Polynomial.eval_X)
         ","
         (Tactic.simpLemma [] [] `Polynomial.map_pow)
         ","
         (Tactic.simpLemma [] [] `Polynomial.eval_C)
         ","
         (Tactic.simpLemma [] [] `Polynomial.eval_pow)
         ","
         (Tactic.simpLemma [] [] `succ_nth_defining_poly)
         ","
         (Tactic.simpLemma [] [] `Polynomial.eval_mul)
         ","
         (Tactic.simpLemma [] [] `Polynomial.eval_add)
         ","
         (Tactic.simpLemma [] [] `Polynomial.eval_sub)
         ","
         (Tactic.simpLemma [] [] `Polynomial.map_mul)
         ","
         (Tactic.simpLemma [] [] `Polynomial.map_sub)
         ","
         (Tactic.simpLemma [] [] `Polynomial.IsRoot.def)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.IsRoot.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.eval_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.eval_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.eval_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `succ_nth_defining_poly
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.eval_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.eval_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.map_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.eval_X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl [] [] ":=" (Term.app `succ_nth_val_spec [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `succ_nth_val_spec [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succ_nth_val_spec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_zero)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_+_»
        («term_+_»
         («term_*_»
          («term_^_» (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]) "^" `p)
          "*"
          («term_^_»
           (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
         "+"
         («term_*_»
          (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "*"
          («term_^_»
           («term_^_» (Term.app `bs [(num "0")]) "^" `p)
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
        "+"
        (Term.app
         `nthRemainder
         [`p
          `n
          (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
          (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])]))
       "="
       («term_+_»
        («term_+_»
         («term_*_»
          (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
          "*"
          («term_^_»
           (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
         "+"
         («term_*_»
          (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
          "*"
          («term_^_»
           (Term.app `bs [(num "0")])
           "^"
           («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
        "+"
        (Term.app
         `nthRemainder
         [`p `n `bs (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₂])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_+_»
        («term_*_»
         (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
         "*"
         («term_^_»
          (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
        "+"
        («term_*_»
         (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         («term_^_»
          (Term.app `bs [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
       "+"
       (Term.app
        `nthRemainder
        [`p `n `bs (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₂])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nthRemainder
       [`p `n `bs (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `truncateFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `a₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nthRemainder
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       («term_*_»
        (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
        "*"
        («term_^_»
         (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
       "+"
       («term_*_»
        (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        («term_^_» (Term.app `bs [(num "0")]) "^" («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       («term_^_» (Term.app `bs [(num "0")]) "^" («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `bs [(num "0")]) "^" («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `bs [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
       "*"
       («term_^_»
        (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
        "^"
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succNthVal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       («term_+_»
        («term_*_»
         («term_^_» (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]) "^" `p)
         "*"
         («term_^_»
          (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
        "+"
        («term_*_»
         (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
         "*"
         («term_^_»
          («term_^_» (Term.app `bs [(num "0")]) "^" `p)
          "^"
          («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
       "+"
       (Term.app
        `nthRemainder
        [`p
         `n
         (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
         (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nthRemainder
       [`p
        `n
        (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
        (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `truncateFun [(«term_+_» `n "+" (num "1")) `a₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `truncateFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `truncateFun [(Term.paren "(" («term_+_» `n "+" (num "1")) ")") `a₁])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `bs [`v]) "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `bs [`v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`v] [] "=>" («term_^_» (Term.app `bs [`v]) "^" `p)))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nthRemainder
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       («term_*_»
        («term_^_» (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]) "^" `p)
        "*"
        («term_^_»
         (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
       "+"
       («term_*_»
        (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
        "*"
        («term_^_»
         («term_^_» (Term.app `bs [(num "0")]) "^" `p)
         "^"
         («term_^_» `p "^" («term_+_» `n "+" (num "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
       "*"
       («term_^_»
        («term_^_» (Term.app `bs [(num "0")]) "^" `p)
        "^"
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       («term_^_» (Term.app `bs [(num "0")]) "^" `p)
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_^_» (Term.app `bs [(num "0")]) "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `bs [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 80, (some 80, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_» (Term.app `bs [(num "0")]) "^" `p)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_»
       («term_^_» (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]) "^" `p)
       "*"
       («term_^_»
        (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
        "^"
        («term_^_» `p "^" («term_+_» `n "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
       "^"
       («term_^_» `p "^" («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂]) "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `succNthVal [`p `n `a₁ `a₂ `bs `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `bs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succNthVal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app `Fin [(«term_+_» `n "+" (num "1"))]) "→" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `Fin [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  succ_nth_val_spec'
  ( n : ℕ )
      ( a₁ a₂ : 𝕎 k )
      ( bs : Fin n + 1 → k )
      ( ha₁ : a₁ . coeff 0 ≠ 0 )
      ( ha₂ : a₂ . coeff 0 ≠ 0 )
    :
      succNthVal p n a₁ a₂ bs ha₁ ha₂ ^ p * a₁ . coeff 0 ^ p ^ n + 1
            +
            a₁ . coeff n + 1 * bs 0 ^ p ^ p ^ n + 1
          +
          nthRemainder p n fun v => bs v ^ p truncateFun n + 1 a₁
        =
        succNthVal p n a₁ a₂ bs ha₁ ha₂ * a₂ . coeff 0 ^ p ^ n + 1
            +
            a₂ . coeff n + 1 * bs 0 ^ p ^ n + 1
          +
          nthRemainder p n bs truncateFun n + 1 a₂
  :=
    by
      rw [ ← sub_eq_zero ]
        have := succ_nth_val_spec p n a₁ a₂ bs ha₁ ha₂
        simp
          only
          [
            Polynomial.map_add
              ,
              Polynomial.eval_X
              ,
              Polynomial.map_pow
              ,
              Polynomial.eval_C
              ,
              Polynomial.eval_pow
              ,
              succ_nth_defining_poly
              ,
              Polynomial.eval_mul
              ,
              Polynomial.eval_add
              ,
              Polynomial.eval_sub
              ,
              Polynomial.map_mul
              ,
              Polynomial.map_sub
              ,
              Polynomial.IsRoot.def
            ]
          at this
        convert this using 1
        ring
#align witt_vector.recursion_main.succ_nth_val_spec' WittVector.RecursionMain.succ_nth_val_spec'

end IsAlgClosed

end RecursionMain

namespace RecursionBase

include hp

variable {k : Type _} [Field k] [IsAlgClosed k]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `solution_pow [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `k]))
         ","
         («term_=_»
          («term_^_» `x "^" («term_-_» `p "-" (num "1")))
          "="
          («term_/_»
           (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
           "/"
           (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]))))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app `IsAlgClosed.exists_pow_nat_eq [(Term.hole "_")])
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(linarith
             "linarith"
             []
             (linarithArgsRest
              []
              []
              ["[" [`hp.out.one_lt "," (Term.app `le_of_lt [`hp.out.one_lt])] "]"]))]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `IsAlgClosed.exists_pow_nat_eq [(Term.hole "_")])
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(linarith
            "linarith"
            []
            (linarithArgsRest
             []
             []
             ["[" [`hp.out.one_lt "," (Term.app `le_of_lt [`hp.out.one_lt])] "]"]))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(linarith
           "linarith"
           []
           (linarithArgsRest
            []
            []
            ["[" [`hp.out.one_lt "," (Term.app `le_of_lt [`hp.out.one_lt])] "]"]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith
       "linarith"
       []
       (linarithArgsRest
        []
        []
        ["[" [`hp.out.one_lt "," (Term.app `le_of_lt [`hp.out.one_lt])] "]"]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_lt [`hp.out.one_lt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.out.one_lt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.out.one_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `IsAlgClosed.exists_pow_nat_eq [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsAlgClosed.exists_pow_nat_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `k]))
       ","
       («term_=_»
        («term_^_» `x "^" («term_-_» `p "-" (num "1")))
        "="
        («term_/_»
         (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
         "/"
         (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_^_» `x "^" («term_-_» `p "-" (num "1")))
       "="
       («term_/_»
        (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
        "/"
        (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
       "/"
       (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_» `x "^" («term_-_» `p "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `p "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `p "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  solution_pow
  ( a₁ a₂ : 𝕎 k ) : ∃ x : k , x ^ p - 1 = a₂ . coeff 0 / a₁ . coeff 0
  := IsAlgClosed.exists_pow_nat_eq _ <| by linarith [ hp.out.one_lt , le_of_lt hp.out.one_lt ]
#align witt_vector.recursion_base.solution_pow WittVector.RecursionBase.solution_pow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The base case (0th coefficient) of our solution vector. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `solution [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         []
         ")")]
       [(Term.typeSpec ":" `k)])
      (Command.declValSimple
       ":="
       («term_<|_» `Classical.choose "<|" (Term.app `solution_pow [`p `a₁ `a₂]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `Classical.choose "<|" (Term.app `solution_pow [`p `a₁ `a₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `solution_pow [`p `a₁ `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solution_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `Classical.choose
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The base case (0th coefficient) of our solution vector. -/
  def solution ( a₁ a₂ : 𝕎 k ) : k := Classical.choose <| solution_pow p a₁ a₂
#align witt_vector.recursion_base.solution WittVector.RecursionBase.solution

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `solution_spec [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_^_» (Term.app `solution [`p `a₁ `a₂]) "^" («term_-_» `p "-" (num "1")))
         "="
         («term_/_»
          (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
          "/"
          (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])))))
      (Command.declValSimple
       ":="
       («term_<|_» `Classical.choose_spec "<|" (Term.app `solution_pow [`p `a₁ `a₂]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `Classical.choose_spec "<|" (Term.app `solution_pow [`p `a₁ `a₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `solution_pow [`p `a₁ `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solution_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `Classical.choose_spec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_^_» (Term.app `solution [`p `a₁ `a₂]) "^" («term_-_» `p "-" (num "1")))
       "="
       («term_/_»
        (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
        "/"
        (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
       "/"
       (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_» (Term.app `solution [`p `a₁ `a₂]) "^" («term_-_» `p "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `p "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `p "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `solution [`p `a₁ `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solution
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  solution_spec
  ( a₁ a₂ : 𝕎 k ) : solution p a₁ a₂ ^ p - 1 = a₂ . coeff 0 / a₁ . coeff 0
  := Classical.choose_spec <| solution_pow p a₁ a₂
#align witt_vector.recursion_base.solution_spec WittVector.RecursionBase.solution_spec

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `solution_nonzero [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         "}")
        (Term.explicitBinder
         "("
         [`ha₁]
         [":" («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₂]
         [":" («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")]
       (Term.typeSpec ":" («term_≠_» (Term.app `solution [`p `a₁ `a₂]) "≠" (num "0"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.intro "intro" [`h])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `solution_spec [`p `a₁ `a₂]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `zero_pow)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `ha₁) "," (Tactic.simpLemma [] [] `ha₂)]
                 "]")]
               ["using" (Term.app `_root_.div_eq_zero_iff.mp [`this.symm])]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(linarith
              "linarith"
              []
              (linarithArgsRest
               []
               []
               ["[" [`hp.out.one_lt "," (Term.app `le_of_lt [`hp.out.one_lt])] "]"]))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`h])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `solution_spec [`p `a₁ `a₂]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `zero_pow)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] `ha₁) "," (Tactic.simpLemma [] [] `ha₂)]
                "]")]
              ["using" (Term.app `_root_.div_eq_zero_iff.mp [`this.symm])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(linarith
             "linarith"
             []
             (linarithArgsRest
              []
              []
              ["[" [`hp.out.one_lt "," (Term.app `le_of_lt [`hp.out.one_lt])] "]"]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(linarith
         "linarith"
         []
         (linarithArgsRest
          []
          []
          ["[" [`hp.out.one_lt "," (Term.app `le_of_lt [`hp.out.one_lt])] "]"]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith
       "linarith"
       []
       (linarithArgsRest
        []
        []
        ["[" [`hp.out.one_lt "," (Term.app `le_of_lt [`hp.out.one_lt])] "]"]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_lt [`hp.out.one_lt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.out.one_lt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.out.one_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          []
          [(Tactic.simpArgs
            "["
            [(Tactic.simpLemma [] [] `ha₁) "," (Tactic.simpLemma [] [] `ha₂)]
            "]")]
          ["using" (Term.app `_root_.div_eq_zero_iff.mp [`this.symm])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `ha₁) "," (Tactic.simpLemma [] [] `ha₂)]
          "]")]
        ["using" (Term.app `_root_.div_eq_zero_iff.mp [`this.symm])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `_root_.div_eq_zero_iff.mp [`this.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `_root_.div_eq_zero_iff.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `zero_pow)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `solution_spec [`p `a₁ `a₂]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `solution_spec [`p `a₁ `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solution_spec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≠_» (Term.app `solution [`p `a₁ `a₂]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `solution [`p `a₁ `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solution
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  solution_nonzero
  { a₁ a₂ : 𝕎 k } ( ha₁ : a₁ . coeff 0 ≠ 0 ) ( ha₂ : a₂ . coeff 0 ≠ 0 ) : solution p a₁ a₂ ≠ 0
  :=
    by
      intro h
        have := solution_spec p a₁ a₂
        rw [ h , zero_pow ] at this
        · simpa [ ha₁ , ha₂ ] using _root_.div_eq_zero_iff.mp this.symm
        · linarith [ hp.out.one_lt , le_of_lt hp.out.one_lt ]
#align witt_vector.recursion_base.solution_nonzero WittVector.RecursionBase.solution_nonzero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `solution_spec' [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`a₁]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         "}")
        (Term.explicitBinder
         "("
         [`ha₁]
         [":" («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_*_»
          («term_^_» (Term.app `solution [`p `a₁ `a₂]) "^" `p)
          "*"
          (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]))
         "="
         («term_*_»
          (Term.app `solution [`p `a₁ `a₂])
          "*"
          (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `solution_spec [`p `a₁ `a₂]))))
           []
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] (Term.app `Nat.exists_eq_succ_of_ne_zero [`hp.out.ne_zero]))]
            []
            ["with" [(Lean.binderIdent `q) (Lean.binderIdent `hq)]])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hq' []]
              [(Term.typeSpec ":" («term_=_» `q "=" («term_-_» `p "-" (num "1"))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `hq)
                     ","
                     (Tactic.simpLemma [] [] `tsub_zero)
                     ","
                     (Tactic.simpLemma [] [] `Nat.succ_sub_succ_eq_sub)]
                    "]"]
                   [])]))))))
           []
           (Mathlib.Tactic.Conv.convLHS
            "conv_lhs"
            []
            []
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(Tactic.Conv.congr "congr")
               []
               (Tactic.Conv.congr "congr")
               []
               (Tactic.Conv.skip "skip")
               []
               (Tactic.Conv.convRw__
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hq)] "]"))])))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `pow_succ')
              ","
              (Tactic.rwRule [] `hq')
              ","
              (Tactic.rwRule [] `this)]
             "]")
            [])
           []
           (Tactic.fieldSimp
            "field_simp"
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `ha₁) "," (Tactic.simpLemma [] [] `mul_comm)]
              "]")]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `solution_spec [`p `a₁ `a₂]))))
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] (Term.app `Nat.exists_eq_succ_of_ne_zero [`hp.out.ne_zero]))]
           []
           ["with" [(Lean.binderIdent `q) (Lean.binderIdent `hq)]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hq' []]
             [(Term.typeSpec ":" («term_=_» `q "=" («term_-_» `p "-" (num "1"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `hq)
                    ","
                    (Tactic.simpLemma [] [] `tsub_zero)
                    ","
                    (Tactic.simpLemma [] [] `Nat.succ_sub_succ_eq_sub)]
                   "]"]
                  [])]))))))
          []
          (Mathlib.Tactic.Conv.convLHS
           "conv_lhs"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(Tactic.Conv.congr "congr")
              []
              (Tactic.Conv.congr "congr")
              []
              (Tactic.Conv.skip "skip")
              []
              (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hq)] "]"))])))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `pow_succ') "," (Tactic.rwRule [] `hq') "," (Tactic.rwRule [] `this)]
            "]")
           [])
          []
          (Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma [] [] `ha₁) "," (Tactic.simpLemma [] [] `mul_comm)]
             "]")]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp
       "field_simp"
       []
       []
       []
       [(Tactic.simpArgs
         "["
         [(Tactic.simpLemma [] [] `ha₁) "," (Tactic.simpLemma [] [] `mul_comm)]
         "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `pow_succ') "," (Tactic.rwRule [] `hq') "," (Tactic.rwRule [] `this)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hq'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_succ'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convLHS
       "conv_lhs"
       []
       []
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.congr "congr")
          []
          (Tactic.Conv.congr "congr")
          []
          (Tactic.Conv.skip "skip")
          []
          (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hq)] "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hq' []]
         [(Term.typeSpec ":" («term_=_» `q "=" («term_-_» `p "-" (num "1"))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `hq)
                ","
                (Tactic.simpLemma [] [] `tsub_zero)
                ","
                (Tactic.simpLemma [] [] `Nat.succ_sub_succ_eq_sub)]
               "]"]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `hq)
             ","
             (Tactic.simpLemma [] [] `tsub_zero)
             ","
             (Tactic.simpLemma [] [] `Nat.succ_sub_succ_eq_sub)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `hq)
         ","
         (Tactic.simpLemma [] [] `tsub_zero)
         ","
         (Tactic.simpLemma [] [] `Nat.succ_sub_succ_eq_sub)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.succ_sub_succ_eq_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tsub_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `q "=" («term_-_» `p "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `p "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] (Term.app `Nat.exists_eq_succ_of_ne_zero [`hp.out.ne_zero]))]
       []
       ["with" [(Lean.binderIdent `q) (Lean.binderIdent `hq)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.exists_eq_succ_of_ne_zero [`hp.out.ne_zero])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.out.ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.exists_eq_succ_of_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `solution_spec [`p `a₁ `a₂]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `solution_spec [`p `a₁ `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solution_spec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_*_»
        («term_^_» (Term.app `solution [`p `a₁ `a₂]) "^" `p)
        "*"
        (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]))
       "="
       («term_*_»
        (Term.app `solution [`p `a₁ `a₂])
        "*"
        (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `solution [`p `a₁ `a₂])
       "*"
       (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `solution [`p `a₁ `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solution
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       («term_^_» (Term.app `solution [`p `a₁ `a₂]) "^" `p)
       "*"
       (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» (Term.app `solution [`p `a₁ `a₂]) "^" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `solution [`p `a₁ `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solution
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  solution_spec'
  { a₁ : 𝕎 k } ( ha₁ : a₁ . coeff 0 ≠ 0 ) ( a₂ : 𝕎 k )
    : solution p a₁ a₂ ^ p * a₁ . coeff 0 = solution p a₁ a₂ * a₂ . coeff 0
  :=
    by
      have := solution_spec p a₁ a₂
        cases' Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero with q hq
        have hq' : q = p - 1 := by simp only [ hq , tsub_zero , Nat.succ_sub_succ_eq_sub ]
        conv_lhs => congr congr skip rw [ hq ]
        rw [ pow_succ' , hq' , this ]
        field_simp [ ha₁ , mul_comm ]
#align witt_vector.recursion_base.solution_spec' WittVector.RecursionBase.solution_spec'

end RecursionBase

open RecursionMain RecursionBase

section FrobeniusRotation

section IsAlgClosed

include hp

variable {k : Type _} [Field k] [CharP k p] [IsAlgClosed k]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Recursively defines the sequence of coefficients for `witt_vector.frobenius_rotation`.\n-/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `frobeniusRotationCoeff [])
      (Command.optDeclSig
       [(Term.implicitBinder
         "{"
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         "}")
        (Term.explicitBinder
         "("
         [`ha₁]
         [":" («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₂]
         [":" («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.arrow (termℕ "ℕ") "→" `k))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(num "0")]] "=>" (Term.app `solution [`p `a₁ `a₂]))
          (Term.matchAlt
           "|"
           [[(«term_+_» `n "+" (num "1"))]]
           "=>"
           (Term.app
            `succNthVal
            [`p
             `n
             `a₁
             `a₂
             (Term.fun
              "fun"
              (Term.basicFun
               [`i]
               []
               "=>"
               (Term.app `frobenius_rotation_coeff [(Term.proj `i "." `val)])))
             `ha₁
             `ha₂]))])
        []))
      []
      []
      [(Command.decreasingBy
        "decreasing_by"
        (Command.terminationHint1
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.apply "apply" `Fin.is_lt)]))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.terminationHint1', expected 'Lean.Parser.Command.terminationHintMany'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `Fin.is_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.is_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `succNthVal
       [`p
        `n
        `a₁
        `a₂
        (Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          (Term.app `frobenius_rotation_coeff [(Term.proj `i "." `val)])))
        `ha₁
        `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun [`i] [] "=>" (Term.app `frobenius_rotation_coeff [(Term.proj `i "." `val)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobenius_rotation_coeff [(Term.proj `i "." `val)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `i "." `val)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius_rotation_coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun [`i] [] "=>" (Term.app `frobenius_rotation_coeff [(Term.proj `i "." `val)])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succNthVal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `solution [`p `a₁ `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solution
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow (termℕ "ℕ") "→" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Recursively defines the sequence of coefficients for `witt_vector.frobenius_rotation`.
      -/
    noncomputable
  def
    frobeniusRotationCoeff
    { a₁ a₂ : 𝕎 k } ( ha₁ : a₁ . coeff 0 ≠ 0 ) ( ha₂ : a₂ . coeff 0 ≠ 0 ) : ℕ → k
    | 0 => solution p a₁ a₂
      | n + 1 => succNthVal p n a₁ a₂ fun i => frobenius_rotation_coeff i . val ha₁ ha₂
    decreasing_by apply Fin.is_lt
#align witt_vector.frobenius_rotation_coeff WittVector.frobeniusRotationCoeff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For nonzero `a₁` and `a₂`, `frobenius_rotation a₁ a₂` is a Witt vector that satisfies the\nequation `frobenius (frobenius_rotation a₁ a₂) * a₁ = (frobenius_rotation a₁ a₂) * a₂`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `frobeniusRotation [])
      (Command.optDeclSig
       [(Term.implicitBinder
         "{"
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         "}")
        (Term.explicitBinder
         "("
         [`ha₁]
         [":" («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₂]
         [":" («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k]))])
      (Command.declValSimple
       ":="
       (Term.app `WittVector.mk [`p (Term.app `frobeniusRotationCoeff [`p `ha₁ `ha₂])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `WittVector.mk [`p (Term.app `frobeniusRotationCoeff [`p `ha₁ `ha₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobeniusRotationCoeff [`p `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobeniusRotationCoeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `frobeniusRotationCoeff [`p `ha₁ `ha₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `WittVector.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    For nonzero `a₁` and `a₂`, `frobenius_rotation a₁ a₂` is a Witt vector that satisfies the
    equation `frobenius (frobenius_rotation a₁ a₂) * a₁ = (frobenius_rotation a₁ a₂) * a₂`.
    -/
  def
    frobeniusRotation
    { a₁ a₂ : 𝕎 k } ( ha₁ : a₁ . coeff 0 ≠ 0 ) ( ha₂ : a₂ . coeff 0 ≠ 0 ) : 𝕎 k
    := WittVector.mk p frobeniusRotationCoeff p ha₁ ha₂
#align witt_vector.frobenius_rotation WittVector.frobeniusRotation

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `frobenius_rotation_nonzero [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         "}")
        (Term.explicitBinder
         "("
         [`ha₁]
         [":" («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₂]
         [":" («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")]
       (Term.typeSpec ":" («term_≠_» (Term.app `frobeniusRotation [`p `ha₁ `ha₂]) "≠" (num "0"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.intro "intro" [`h])
           []
           (Tactic.apply "apply" (Term.app `solution_nonzero [`p `ha₁ `ha₂]))
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `h)
                ","
                (Tactic.simpLemma [] [] `frobenius_rotation)
                ","
                (Tactic.simpLemma [] [] `frobenius_rotation_coeff)]
               "]")]
             ["using" (Term.app `WittVector.zero_coeff [`p `k (num "0")])]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`h])
          []
          (Tactic.apply "apply" (Term.app `solution_nonzero [`p `ha₁ `ha₂]))
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `h)
               ","
               (Tactic.simpLemma [] [] `frobenius_rotation)
               ","
               (Tactic.simpLemma [] [] `frobenius_rotation_coeff)]
              "]")]
            ["using" (Term.app `WittVector.zero_coeff [`p `k (num "0")])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `h)
           ","
           (Tactic.simpLemma [] [] `frobenius_rotation)
           ","
           (Tactic.simpLemma [] [] `frobenius_rotation_coeff)]
          "]")]
        ["using" (Term.app `WittVector.zero_coeff [`p `k (num "0")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `WittVector.zero_coeff [`p `k (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `WittVector.zero_coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_rotation_coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `solution_nonzero [`p `ha₁ `ha₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `solution_nonzero [`p `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solution_nonzero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≠_» (Term.app `frobeniusRotation [`p `ha₁ `ha₂]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `frobeniusRotation [`p `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobeniusRotation
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  frobenius_rotation_nonzero
  { a₁ a₂ : 𝕎 k } ( ha₁ : a₁ . coeff 0 ≠ 0 ) ( ha₂ : a₂ . coeff 0 ≠ 0 )
    : frobeniusRotation p ha₁ ha₂ ≠ 0
  :=
    by
      intro h
        apply solution_nonzero p ha₁ ha₂
        simpa
          [ ← h , frobenius_rotation , frobenius_rotation_coeff ] using WittVector.zero_coeff p k 0
#align witt_vector.frobenius_rotation_nonzero WittVector.frobenius_rotation_nonzero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `frobenius_frobenius_rotation [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`a₁ `a₂]
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         "}")
        (Term.explicitBinder
         "("
         [`ha₁]
         [":" («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`ha₂]
         [":" («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_*_» (Term.app `frobenius [(Term.app `frobeniusRotation [`p `ha₁ `ha₂])]) "*" `a₁)
         "="
         («term_*_» (Term.app `frobeniusRotation [`p `ha₁ `ha₂]) "*" `a₂))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
            [])
           []
           (Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `n)]
            []
            ["with" [(Lean.binderIdent `n) (Lean.binderIdent `ih)]]
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `WittVector.mul_coeff_zero)
                ","
                (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)
                ","
                (Tactic.simpLemma [] [] `frobenius_rotation)
                ","
                (Tactic.simpLemma [] [] `frobenius_rotation_coeff)]
               "]"]
              [])
             []
             (Tactic.apply "apply" (Term.app `solution_spec' [(Term.hole "_") `ha₁]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `nth_remainder_spec)
                ","
                (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)
                ","
                (Tactic.simpLemma [] [] `frobenius_rotation_coeff)
                ","
                (Tactic.simpLemma [] [] `frobenius_rotation)
                ","
                (Tactic.simpLemma [] [] `Fin.val_eq_coe)]
               "]"]
              [])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                []
                ":="
                (Term.app
                 `succ_nth_val_spec'
                 [`p
                  `n
                  `a₁
                  `a₂
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`i]
                    [(Term.typeSpec ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]
                    "=>"
                    (Term.app `frobenius_rotation_coeff [`p `ha₁ `ha₂ (Term.proj `i "." `val)])))
                  `ha₁
                  `ha₂]))))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `frobenius_rotation_coeff)
                ","
                (Tactic.simpLemma [] [] `Fin.val_eq_coe)
                ","
                (Tactic.simpLemma [] [] `Fin.val_zero)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
             []
             (convert "convert" [] `this ["using" (num "4")])
             []
             (Tactic.apply "apply" `TruncatedWittVector.ext)
             []
             (Tactic.intro "intro" [`i])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Fin.val_eq_coe)
                ","
                (Tactic.simpLemma [] [] `WittVector.coeff_truncate_fun)
                ","
                (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)]
               "]"]
              [])
             []
             (Tactic.tacticRfl "rfl")])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
           [])
          []
          (Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `n)]
           []
           ["with" [(Lean.binderIdent `n) (Lean.binderIdent `ih)]]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `WittVector.mul_coeff_zero)
               ","
               (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)
               ","
               (Tactic.simpLemma [] [] `frobenius_rotation)
               ","
               (Tactic.simpLemma [] [] `frobenius_rotation_coeff)]
              "]"]
             [])
            []
            (Tactic.apply "apply" (Term.app `solution_spec' [(Term.hole "_") `ha₁]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `nth_remainder_spec)
               ","
               (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)
               ","
               (Tactic.simpLemma [] [] `frobenius_rotation_coeff)
               ","
               (Tactic.simpLemma [] [] `frobenius_rotation)
               ","
               (Tactic.simpLemma [] [] `Fin.val_eq_coe)]
              "]"]
             [])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               []
               ":="
               (Term.app
                `succ_nth_val_spec'
                [`p
                 `n
                 `a₁
                 `a₂
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`i]
                   [(Term.typeSpec ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]
                   "=>"
                   (Term.app `frobenius_rotation_coeff [`p `ha₁ `ha₂ (Term.proj `i "." `val)])))
                 `ha₁
                 `ha₂]))))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `frobenius_rotation_coeff)
               ","
               (Tactic.simpLemma [] [] `Fin.val_eq_coe)
               ","
               (Tactic.simpLemma [] [] `Fin.val_zero)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
            []
            (convert "convert" [] `this ["using" (num "4")])
            []
            (Tactic.apply "apply" `TruncatedWittVector.ext)
            []
            (Tactic.intro "intro" [`i])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Fin.val_eq_coe)
               ","
               (Tactic.simpLemma [] [] `WittVector.coeff_truncate_fun)
               ","
               (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)]
              "]"]
             [])
            []
            (Tactic.tacticRfl "rfl")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `nth_remainder_spec)
           ","
           (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)
           ","
           (Tactic.simpLemma [] [] `frobenius_rotation_coeff)
           ","
           (Tactic.simpLemma [] [] `frobenius_rotation)
           ","
           (Tactic.simpLemma [] [] `Fin.val_eq_coe)]
          "]"]
         [])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           []
           ":="
           (Term.app
            `succ_nth_val_spec'
            [`p
             `n
             `a₁
             `a₂
             (Term.fun
              "fun"
              (Term.basicFun
               [`i]
               [(Term.typeSpec ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]
               "=>"
               (Term.app `frobenius_rotation_coeff [`p `ha₁ `ha₂ (Term.proj `i "." `val)])))
             `ha₁
             `ha₂]))))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `frobenius_rotation_coeff)
           ","
           (Tactic.simpLemma [] [] `Fin.val_eq_coe)
           ","
           (Tactic.simpLemma [] [] `Fin.val_zero)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
        []
        (convert "convert" [] `this ["using" (num "4")])
        []
        (Tactic.apply "apply" `TruncatedWittVector.ext)
        []
        (Tactic.intro "intro" [`i])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Fin.val_eq_coe)
           ","
           (Tactic.simpLemma [] [] `WittVector.coeff_truncate_fun)
           ","
           (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)]
          "]"]
         [])
        []
        (Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Fin.val_eq_coe)
         ","
         (Tactic.simpLemma [] [] `WittVector.coeff_truncate_fun)
         ","
         (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WittVector.coeff_frobenius_char_p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WittVector.coeff_truncate_fun
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`i])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `TruncatedWittVector.ext)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TruncatedWittVector.ext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `this ["using" (num "4")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `frobenius_rotation_coeff)
         ","
         (Tactic.simpLemma [] [] `Fin.val_eq_coe)
         ","
         (Tactic.simpLemma [] [] `Fin.val_zero)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.val_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_rotation_coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app
          `succ_nth_val_spec'
          [`p
           `n
           `a₁
           `a₂
           (Term.fun
            "fun"
            (Term.basicFun
             [`i]
             [(Term.typeSpec ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]
             "=>"
             (Term.app `frobenius_rotation_coeff [`p `ha₁ `ha₂ (Term.proj `i "." `val)])))
           `ha₁
           `ha₂]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `succ_nth_val_spec'
       [`p
        `n
        `a₁
        `a₂
        (Term.fun
         "fun"
         (Term.basicFun
          [`i]
          [(Term.typeSpec ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]
          "=>"
          (Term.app `frobenius_rotation_coeff [`p `ha₁ `ha₂ (Term.proj `i "." `val)])))
        `ha₁
        `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        [(Term.typeSpec ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]
        "=>"
        (Term.app `frobenius_rotation_coeff [`p `ha₁ `ha₂ (Term.proj `i "." `val)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobenius_rotation_coeff [`p `ha₁ `ha₂ (Term.proj `i "." `val)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `i "." `val)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius_rotation_coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`i]
       [(Term.typeSpec ":" (Term.app `Fin [(Term.paren "(" («term_+_» `n "+" (num "1")) ")")]))]
       "=>"
       (Term.app `frobenius_rotation_coeff [`p `ha₁ `ha₂ (Term.proj `i "." `val)])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succ_nth_val_spec'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `nth_remainder_spec)
         ","
         (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)
         ","
         (Tactic.simpLemma [] [] `frobenius_rotation_coeff)
         ","
         (Tactic.simpLemma [] [] `frobenius_rotation)
         ","
         (Tactic.simpLemma [] [] `Fin.val_eq_coe)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_rotation_coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WittVector.coeff_frobenius_char_p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nth_remainder_spec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `WittVector.mul_coeff_zero)
           ","
           (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)
           ","
           (Tactic.simpLemma [] [] `frobenius_rotation)
           ","
           (Tactic.simpLemma [] [] `frobenius_rotation_coeff)]
          "]"]
         [])
        []
        (Tactic.apply "apply" (Term.app `solution_spec' [(Term.hole "_") `ha₁]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `solution_spec' [(Term.hole "_") `ha₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `solution_spec' [(Term.hole "_") `ha₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solution_spec'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `WittVector.mul_coeff_zero)
         ","
         (Tactic.simpLemma [] [] `WittVector.coeff_frobenius_char_p)
         ","
         (Tactic.simpLemma [] [] `frobenius_rotation)
         ","
         (Tactic.simpLemma [] [] `frobenius_rotation_coeff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_rotation_coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_rotation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WittVector.coeff_frobenius_char_p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WittVector.mul_coeff_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `n)]
       []
       ["with" [(Lean.binderIdent `n) (Lean.binderIdent `ih)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_*_» (Term.app `frobenius [(Term.app `frobeniusRotation [`p `ha₁ `ha₂])]) "*" `a₁)
       "="
       («term_*_» (Term.app `frobeniusRotation [`p `ha₁ `ha₂]) "*" `a₂))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.app `frobeniusRotation [`p `ha₁ `ha₂]) "*" `a₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `frobeniusRotation [`p `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobeniusRotation
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» (Term.app `frobenius [(Term.app `frobeniusRotation [`p `ha₁ `ha₂])]) "*" `a₁)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `frobenius [(Term.app `frobeniusRotation [`p `ha₁ `ha₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobeniusRotation [`p `ha₁ `ha₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobeniusRotation
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `frobeniusRotation [`p `ha₁ `ha₂])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₂ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₂ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₂ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.app (Term.proj `a₁ "." `coeff) [(num "0")]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj `a₁ "." `coeff) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `a₁ "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  frobenius_frobenius_rotation
  { a₁ a₂ : 𝕎 k } ( ha₁ : a₁ . coeff 0 ≠ 0 ) ( ha₂ : a₂ . coeff 0 ≠ 0 )
    : frobenius frobeniusRotation p ha₁ ha₂ * a₁ = frobeniusRotation p ha₁ ha₂ * a₂
  :=
    by
      ext n
        induction' n with n ih
        ·
          simp
              only
              [
                WittVector.mul_coeff_zero
                  ,
                  WittVector.coeff_frobenius_char_p
                  ,
                  frobenius_rotation
                  ,
                  frobenius_rotation_coeff
                ]
            apply solution_spec' _ ha₁
        ·
          simp
              only
              [
                nth_remainder_spec
                  ,
                  WittVector.coeff_frobenius_char_p
                  ,
                  frobenius_rotation_coeff
                  ,
                  frobenius_rotation
                  ,
                  Fin.val_eq_coe
                ]
            have
              :=
                succ_nth_val_spec'
                  p n a₁ a₂ fun i : Fin n + 1 => frobenius_rotation_coeff p ha₁ ha₂ i . val ha₁ ha₂
            simp only [ frobenius_rotation_coeff , Fin.val_eq_coe , Fin.val_zero ] at this
            convert this using 4
            apply TruncatedWittVector.ext
            intro i
            simp
              only
              [ Fin.val_eq_coe , WittVector.coeff_truncate_fun , WittVector.coeff_frobenius_char_p ]
            rfl
#align witt_vector.frobenius_frobenius_rotation WittVector.frobenius_frobenius_rotation

-- mathport name: exprφ
local notation "φ" => IsFractionRing.fieldEquivOfRingEquiv (frobeniusEquiv p k)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_frobenius_solution_fraction_ring_aux [])
      (Command.declSig
       [(Term.explicitBinder "(" [`m `n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`r' `q']
         [":" (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hr']
         [":" («term_≠_» (Term.app (Term.proj `r' "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hq']
         [":" («term_≠_» (Term.app (Term.proj `q' "." `coeff) [(num "0")]) "≠" (num "0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hq]
         [":"
          («term_∈_»
           («term_*_» («term_^_» (coeNotation "↑" `p) "^" `n) "*" `q')
           "∈"
           (Term.app
            `nonZeroDivisors
            [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.let
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `b
           []
           [(Term.typeSpec
             ":"
             (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k]))]
           ":="
           (Term.app `frobeniusRotation [`p `hr' `hq'])))
         []
         («term_=_»
          («term_*_»
           (Term.app
            `IsFractionRing.fieldEquivOfRingEquiv
            [(Term.app `frobeniusEquiv [`p `k])
             (Term.app
              `algebraMap
              [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
               (Term.app
                `FractionRing
                [(Term.app
                  (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                  [`k])])
               `b])])
           "*"
           (Term.app
            `Localization.mk
            [(«term_*_» («term_^_» (coeNotation "↑" `p) "^" `m) "*" `r')
             (Term.anonymousCtor
              "⟨"
              [(«term_*_» («term_^_» (coeNotation "↑" `p) "^" `n) "*" `q') "," `hq]
              "⟩")]))
          "="
          («term_*_»
           («term_^_»
            (coeNotation "↑" `p)
            "^"
            (Term.typeAscription "(" («term_-_» `m "-" `n) ":" [(termℤ "ℤ")] ")"))
           "*"
           (Term.app
            `algebraMap
            [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
             (Term.app
              `FractionRing
              [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])])
             `b]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.intro "intro" [`b])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`key []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 («term_*_»
                  («term_*_»
                   («term_*_» (Term.app `WittVector.frobenius [`b]) "*" («term_^_» `p "^" `m))
                   "*"
                   `r')
                  "*"
                  («term_^_» `p "^" `n))
                 "="
                 («term_*_»
                  («term_*_» («term_^_» `p "^" `m) "*" `b)
                  "*"
                  («term_*_» («term_^_» `p "^" `n) "*" `q'))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`H []]
                     []
                     ":="
                     (Term.app
                      `congr_arg
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [`x]
                         [(Term.typeSpec
                           ":"
                           (Term.app
                            (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                            [`k]))]
                         "=>"
                         («term_*_»
                          («term_*_» `x "*" («term_^_» `p "^" `m))
                          "*"
                          («term_^_» `p "^" `n))))
                       (Term.app `frobenius_frobenius_rotation [`p `hr' `hq'])]))))
                  []
                  (Tactic.dsimp
                   "dsimp"
                   []
                   []
                   []
                   []
                   [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
                  []
                  (Tactic.«tactic_<;>_»
                   (Tactic.refine'
                    "refine'"
                    (Term.app
                     (Term.proj (Term.app `Eq.trans [(Term.hole "_") `H]) "." `trans)
                     [(Term.hole "_")]))
                   "<;>"
                   (Mathlib.Tactic.RingNF.ring "ring"))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hq'' []]
              [(Term.typeSpec
                ":"
                («term_≠_»
                 (Term.app
                  `algebraMap
                  [(Term.app
                    (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                    [`k])
                   (Term.app
                    `FractionRing
                    [(Term.app
                      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                      [`k])])
                   `q'])
                 "≠"
                 (num "0")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hq''' []]
                     [(Term.typeSpec ":" («term_≠_» `q' "≠" (num "0")))]
                     ":="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`h]
                       []
                       "=>"
                       (Term.app
                        `hq'
                        [(Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.simp
                              "simp"
                              []
                              []
                              []
                              ["[" [(Tactic.simpLemma [] [] `h)] "]"]
                              [])])))]))))))
                  []
                  (Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    ["only"]
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [] `Ne.def) "," (Tactic.simpLemma [] [] `map_zero)]
                      "]")]
                    ["using"
                     (Term.app
                      (Term.proj
                       (Term.app
                        `IsFractionRing.injective
                        [(Term.app
                          (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                          [`k])
                         (Term.app
                          `FractionRing
                          [(Term.app
                            (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                            [`k])])])
                       "."
                       `Ne)
                      [`hq'''])]))]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app `zpow_sub₀ [(Term.app `fraction_ring.p_nonzero [`p `k])]))]
             "]")
            [])
           []
           (Tactic.fieldSimp
            "field_simp"
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] (Term.app `fraction_ring.p_nonzero [`p `k]))]
              "]")]
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `IsFractionRing.fieldEquivOfRingEquiv)
              ","
              (Tactic.simpLemma [] [] `IsLocalization.ring_equiv_of_ring_equiv_eq)
              ","
              (Tactic.simpLemma [] [] `RingEquiv.coe_ofBijective)]
             "]"]
            [])
           []
           (convert
            "convert"
            []
            (Term.app
             `congr_arg
             [(Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Term.app
                 `algebraMap
                 [(Term.app
                   (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                   [`k])
                  (Term.app
                   `FractionRing
                   [(Term.app
                     (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                     [`k])])
                  `x])))
              `key])
            ["using" (num "1")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `RingHom.map_mul)
                ","
                (Tactic.simpLemma [] [] `RingHom.map_pow)
                ","
                (Tactic.simpLemma [] [] `map_nat_cast)
                ","
                (Tactic.simpLemma [] [] `frobenius_equiv_apply)]
               "]"]
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `RingHom.map_mul)
                ","
                (Tactic.simpLemma [] [] `RingHom.map_pow)
                ","
                (Tactic.simpLemma [] [] `map_nat_cast)]
               "]"]
              [])])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`b])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`key []]
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_*_»
                 («term_*_»
                  («term_*_» (Term.app `WittVector.frobenius [`b]) "*" («term_^_» `p "^" `m))
                  "*"
                  `r')
                 "*"
                 («term_^_» `p "^" `n))
                "="
                («term_*_»
                 («term_*_» («term_^_» `p "^" `m) "*" `b)
                 "*"
                 («term_*_» («term_^_» `p "^" `n) "*" `q'))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`H []]
                    []
                    ":="
                    (Term.app
                     `congr_arg
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`x]
                        [(Term.typeSpec
                          ":"
                          (Term.app
                           (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                           [`k]))]
                        "=>"
                        («term_*_»
                         («term_*_» `x "*" («term_^_» `p "^" `m))
                         "*"
                         («term_^_» `p "^" `n))))
                      (Term.app `frobenius_frobenius_rotation [`p `hr' `hq'])]))))
                 []
                 (Tactic.dsimp
                  "dsimp"
                  []
                  []
                  []
                  []
                  [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
                 []
                 (Tactic.«tactic_<;>_»
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    (Term.proj (Term.app `Eq.trans [(Term.hole "_") `H]) "." `trans)
                    [(Term.hole "_")]))
                  "<;>"
                  (Mathlib.Tactic.RingNF.ring "ring"))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hq'' []]
             [(Term.typeSpec
               ":"
               («term_≠_»
                (Term.app
                 `algebraMap
                 [(Term.app
                   (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                   [`k])
                  (Term.app
                   `FractionRing
                   [(Term.app
                     (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                     [`k])])
                  `q'])
                "≠"
                (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hq''' []]
                    [(Term.typeSpec ":" («term_≠_» `q' "≠" (num "0")))]
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`h]
                      []
                      "=>"
                      (Term.app
                       `hq'
                       [(Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.simp
                             "simp"
                             []
                             []
                             []
                             ["[" [(Tactic.simpLemma [] [] `h)] "]"]
                             [])])))]))))))
                 []
                 (Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   ["only"]
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [] `Ne.def) "," (Tactic.simpLemma [] [] `map_zero)]
                     "]")]
                   ["using"
                    (Term.app
                     (Term.proj
                      (Term.app
                       `IsFractionRing.injective
                       [(Term.app
                         (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                         [`k])
                        (Term.app
                         `FractionRing
                         [(Term.app
                           (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                           [`k])])])
                      "."
                      `Ne)
                     [`hq'''])]))]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `zpow_sub₀ [(Term.app `fraction_ring.p_nonzero [`p `k])]))]
            "]")
           [])
          []
          (Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma [] [] (Term.app `fraction_ring.p_nonzero [`p `k]))]
             "]")]
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `IsFractionRing.fieldEquivOfRingEquiv)
             ","
             (Tactic.simpLemma [] [] `IsLocalization.ring_equiv_of_ring_equiv_eq)
             ","
             (Tactic.simpLemma [] [] `RingEquiv.coe_ofBijective)]
            "]"]
           [])
          []
          (convert
           "convert"
           []
           (Term.app
            `congr_arg
            [(Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Term.app
                `algebraMap
                [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
                 (Term.app
                  `FractionRing
                  [(Term.app
                    (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
                    [`k])])
                 `x])))
             `key])
           ["using" (num "1")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `RingHom.map_mul)
               ","
               (Tactic.simpLemma [] [] `RingHom.map_pow)
               ","
               (Tactic.simpLemma [] [] `map_nat_cast)
               ","
               (Tactic.simpLemma [] [] `frobenius_equiv_apply)]
              "]"]
             [])
            []
            (Mathlib.Tactic.RingNF.ring "ring")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `RingHom.map_mul)
               ","
               (Tactic.simpLemma [] [] `RingHom.map_pow)
               ","
               (Tactic.simpLemma [] [] `map_nat_cast)]
              "]"]
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `RingHom.map_mul)
           ","
           (Tactic.simpLemma [] [] `RingHom.map_pow)
           ","
           (Tactic.simpLemma [] [] `map_nat_cast)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `RingHom.map_mul)
         ","
         (Tactic.simpLemma [] [] `RingHom.map_pow)
         ","
         (Tactic.simpLemma [] [] `map_nat_cast)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_nat_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `RingHom.map_mul)
           ","
           (Tactic.simpLemma [] [] `RingHom.map_pow)
           ","
           (Tactic.simpLemma [] [] `map_nat_cast)
           ","
           (Tactic.simpLemma [] [] `frobenius_equiv_apply)]
          "]"]
         [])
        []
        (Mathlib.Tactic.RingNF.ring "ring")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `RingHom.map_mul)
         ","
         (Tactic.simpLemma [] [] `RingHom.map_pow)
         ","
         (Tactic.simpLemma [] [] `map_nat_cast)
         ","
         (Tactic.simpLemma [] [] `frobenius_equiv_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `frobenius_equiv_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_nat_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `congr_arg
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app
            `algebraMap
            [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
             (Term.app
              `FractionRing
              [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])])
             `x])))
         `key])
       ["using" (num "1")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app
           `algebraMap
           [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
            (Term.app
             `FractionRing
             [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])])
            `x])))
        `key])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `key
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app
         `algebraMap
         [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
          (Term.app
           `FractionRing
           [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])])
          `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `algebraMap
       [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
        (Term.app
         `FractionRing
         [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])])
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `FractionRing
       [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  exists_frobenius_solution_fraction_ring_aux
  ( m n : ℕ )
      ( r' q' : 𝕎 k )
      ( hr' : r' . coeff 0 ≠ 0 )
      ( hq' : q' . coeff 0 ≠ 0 )
      ( hq : ↑ p ^ n * q' ∈ nonZeroDivisors 𝕎 k )
    :
      let
        b : 𝕎 k := frobeniusRotation p hr' hq'
        IsFractionRing.fieldEquivOfRingEquiv frobeniusEquiv p k algebraMap 𝕎 k FractionRing 𝕎 k b
            *
            Localization.mk ↑ p ^ m * r' ⟨ ↑ p ^ n * q' , hq ⟩
          =
          ↑ p ^ ( m - n : ℤ ) * algebraMap 𝕎 k FractionRing 𝕎 k b
  :=
    by
      intro b
        have
          key
            : WittVector.frobenius b * p ^ m * r' * p ^ n = p ^ m * b * p ^ n * q'
            :=
            by
              have
                  H
                    :=
                    congr_arg
                      fun x : 𝕎 k => x * p ^ m * p ^ n frobenius_frobenius_rotation p hr' hq'
                dsimp at H
                refine' Eq.trans _ H . trans _ <;> ring
        have
          hq''
            : algebraMap 𝕎 k FractionRing 𝕎 k q' ≠ 0
            :=
            by
              have hq''' : q' ≠ 0 := fun h => hq' by simp [ h ]
                simpa
                  only
                    [ Ne.def , map_zero ]
                    using IsFractionRing.injective 𝕎 k FractionRing 𝕎 k . Ne hq'''
        rw [ zpow_sub₀ fraction_ring.p_nonzero p k ]
        field_simp [ fraction_ring.p_nonzero p k ]
        simp
          only
          [
            IsFractionRing.fieldEquivOfRingEquiv
              ,
              IsLocalization.ring_equiv_of_ring_equiv_eq
              ,
              RingEquiv.coe_ofBijective
            ]
        convert congr_arg fun x => algebraMap 𝕎 k FractionRing 𝕎 k x key using 1
        ·
          simp only [ RingHom.map_mul , RingHom.map_pow , map_nat_cast , frobenius_equiv_apply ]
            ring
        · simp only [ RingHom.map_mul , RingHom.map_pow , map_nat_cast ]
#align
  witt_vector.exists_frobenius_solution_fraction_ring_aux WittVector.exists_frobenius_solution_fraction_ring_aux

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_frobenius_solution_fraction_ring [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`a]
         [":"
          (Term.app
           `FractionRing
           [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])])]
         "}")
        (Term.explicitBinder "(" [`ha] [":" («term_≠_» `a "≠" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders
            "("
            [(Lean.binderIdent `b)]
            ":"
            (Term.app
             `FractionRing
             [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])])
            ")")
           (Lean.bracketedExplicitBinders
            "("
            [(Lean.binderIdent `hb)]
            ":"
            («term_≠_» `b "≠" (num "0"))
            ")")
           (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `m)] ":" (termℤ "ℤ") ")")])
         ","
         («term_=_»
          («term_*_»
           (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.termφ "φ") [`b])
           "*"
           `a)
          "="
          («term_*_» («term_^_» `p "^" `m) "*" `b)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.revert "revert" [`ha])
           []
           (Tactic.refine' "refine'" (Term.app `Localization.induction_on [`a (Term.hole "_")]))
           []
           (Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq)])
                 [])]
               "⟩"))
             (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `hrq))]
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hq0 []]
              [(Term.typeSpec ":" («term_≠_» `q "≠" (num "0")))]
              ":="
              (Term.app (Term.proj `mem_non_zero_divisors_iff_ne_zero "." (fieldIdx "1")) [`hq]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hr0 []]
              [(Term.typeSpec ":" («term_≠_» `r "≠" (num "0")))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`h]
                []
                "=>"
                (Term.app
                 `hrq
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       []
                       ["[" [(Tactic.simpLemma [] [] `h)] "]"]
                       [])])))]))))))
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r')])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr')])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])]
            []
            [":=" [(Term.app `exists_eq_pow_p_mul [`r `hr0])]])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q')])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq')])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])]
            []
            [":=" [(Term.app `exists_eq_pow_p_mul [`q `hq0])]])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl `b [] [] ":=" (Term.app `frobenius_rotation [`p `hr' `hq']))))
           []
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.app
               `algebraMap
               [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
                (Term.hole "_")
                `b])
              ","
              (Term.hole "_")
              ","
              («term_-_» `m "-" `n)
              ","
              (Term.hole "_")]
             "⟩"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               ["only"]
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `map_zero)] "]")]
               ["using"
                (Term.app
                 (Term.proj
                  (Term.app
                   `IsFractionRing.injective
                   [(Term.app `WittVector [`p `k])
                    (Term.app `FractionRing [(Term.app `WittVector [`p `k])])])
                  "."
                  `Ne)
                 [(Term.app `frobenius_rotation_nonzero [`p `hr' `hq'])])]))])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `exists_frobenius_solution_fraction_ring_aux
             [`p `m `n `r' `q' `hr' `hq' `hq]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.revert "revert" [`ha])
          []
          (Tactic.refine' "refine'" (Term.app `Localization.induction_on [`a (Term.hole "_")]))
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq)])
                [])]
              "⟩"))
            (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `hrq))]
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hq0 []]
             [(Term.typeSpec ":" («term_≠_» `q "≠" (num "0")))]
             ":="
             (Term.app (Term.proj `mem_non_zero_divisors_iff_ne_zero "." (fieldIdx "1")) [`hq]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hr0 []]
             [(Term.typeSpec ":" («term_≠_» `r "≠" (num "0")))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`h]
               []
               "=>"
               (Term.app
                `hrq
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["[" [(Tactic.simpLemma [] [] `h)] "]"]
                      [])])))]))))))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r')])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr')])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app `exists_eq_pow_p_mul [`r `hr0])]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q')])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq')])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app `exists_eq_pow_p_mul [`q `hq0])]])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl `b [] [] ":=" (Term.app `frobenius_rotation [`p `hr' `hq']))))
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.app
              `algebraMap
              [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
               (Term.hole "_")
               `b])
             ","
             (Term.hole "_")
             ","
             («term_-_» `m "-" `n)
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              ["only"]
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `map_zero)] "]")]
              ["using"
               (Term.app
                (Term.proj
                 (Term.app
                  `IsFractionRing.injective
                  [(Term.app `WittVector [`p `k])
                   (Term.app `FractionRing [(Term.app `WittVector [`p `k])])])
                 "."
                 `Ne)
                [(Term.app `frobenius_rotation_nonzero [`p `hr' `hq'])])]))])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `exists_frobenius_solution_fraction_ring_aux
            [`p `m `n `r' `q' `hr' `hq' `hq]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `exists_frobenius_solution_fraction_ring_aux [`p `m `n `r' `q' `hr' `hq' `hq]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `exists_frobenius_solution_fraction_ring_aux [`p `m `n `r' `q' `hr' `hq' `hq])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hq
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hq'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hr'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exists_frobenius_solution_fraction_ring_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          ["only"]
          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `map_zero)] "]")]
          ["using"
           (Term.app
            (Term.proj
             (Term.app
              `IsFractionRing.injective
              [(Term.app `WittVector [`p `k])
               (Term.app `FractionRing [(Term.app `WittVector [`p `k])])])
             "."
             `Ne)
            [(Term.app `frobenius_rotation_nonzero [`p `hr' `hq'])])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `map_zero)] "]")]
        ["using"
         (Term.app
          (Term.proj
           (Term.app
            `IsFractionRing.injective
            [(Term.app `WittVector [`p `k])
             (Term.app `FractionRing [(Term.app `WittVector [`p `k])])])
           "."
           `Ne)
          [(Term.app `frobenius_rotation_nonzero [`p `hr' `hq'])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `IsFractionRing.injective
         [(Term.app `WittVector [`p `k]) (Term.app `FractionRing [(Term.app `WittVector [`p `k])])])
        "."
        `Ne)
       [(Term.app `frobenius_rotation_nonzero [`p `hr' `hq'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `frobenius_rotation_nonzero [`p `hr' `hq'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hq'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hr'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `frobenius_rotation_nonzero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `frobenius_rotation_nonzero [`p `hr' `hq'])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `IsFractionRing.injective
        [(Term.app `WittVector [`p `k]) (Term.app `FractionRing [(Term.app `WittVector [`p `k])])])
       "."
       `Ne)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `IsFractionRing.injective
       [(Term.app `WittVector [`p `k]) (Term.app `FractionRing [(Term.app `WittVector [`p `k])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `FractionRing [(Term.app `WittVector [`p `k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `WittVector [`p `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `WittVector
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `WittVector [`p `k]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `FractionRing
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `FractionRing [(Term.paren "(" (Term.app `WittVector [`p `k]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `WittVector [`p `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `WittVector
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `WittVector [`p `k]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsFractionRing.injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `IsFractionRing.injective
      [(Term.paren "(" (Term.app `WittVector [`p `k]) ")")
       (Term.paren
        "("
        (Term.app `FractionRing [(Term.paren "(" (Term.app `WittVector [`p `k]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.app
          `algebraMap
          [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
           (Term.hole "_")
           `b])
         ","
         (Term.hole "_")
         ","
         («term_-_» `m "-" `n)
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `algebraMap
         [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
          (Term.hole "_")
          `b])
        ","
        (Term.hole "_")
        ","
        («term_-_» `m "-" `n)
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `m "-" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `algebraMap
       [(Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
        (Term.hole "_")
        `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎', expected 'WittVector.RingTheory.WittVector.FrobeniusFractionField.term𝕎._@.RingTheory.WittVector.FrobeniusFractionField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  exists_frobenius_solution_fraction_ring
  { a : FractionRing 𝕎 k } ( ha : a ≠ 0 )
    : ∃ ( b : FractionRing 𝕎 k ) ( hb : b ≠ 0 ) ( m : ℤ ) , φ b * a = p ^ m * b
  :=
    by
      revert ha
        refine' Localization.induction_on a _
        rintro ⟨ r , q , hq ⟩ hrq
        have hq0 : q ≠ 0 := mem_non_zero_divisors_iff_ne_zero . 1 hq
        have hr0 : r ≠ 0 := fun h => hrq by simp [ h ]
        obtain ⟨ m , r' , hr' , rfl ⟩ := exists_eq_pow_p_mul r hr0
        obtain ⟨ n , q' , hq' , rfl ⟩ := exists_eq_pow_p_mul q hq0
        let b := frobenius_rotation p hr' hq'
        refine' ⟨ algebraMap 𝕎 k _ b , _ , m - n , _ ⟩
        ·
          simpa
            only
              [ map_zero ]
              using
                IsFractionRing.injective WittVector p k FractionRing WittVector p k . Ne
                  frobenius_rotation_nonzero p hr' hq'
        exact exists_frobenius_solution_fraction_ring_aux p m n r' q' hr' hq' hq
#align
  witt_vector.exists_frobenius_solution_fraction_ring WittVector.exists_frobenius_solution_fraction_ring

end IsAlgClosed

end FrobeniusRotation

end WittVector

