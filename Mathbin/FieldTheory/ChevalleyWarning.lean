/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module field_theory.chevalley_warning
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.FieldTheory.Finite.Basic

/-!
# The Chevalley–Warning theorem

This file contains a proof of the Chevalley–Warning theorem.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Main results

1. Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
   such that the total degree of `f` is less than `(q-1)` times the cardinality of `σ`.
   Then the evaluation of `f` on all points of `σ → K` (aka `K^σ`) sums to `0`.
   (`sum_mv_polynomial_eq_zero`)
2. The Chevalley–Warning theorem (`char_dvd_card_solutions`).
   Let `f i` be a finite family of multivariate polynomials
   in finitely many variables (`X s`, `s : σ`) such that
   the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
   Then the number of common solutions of the `f i`
   is divisible by the characteristic of `K`.

## Notation

- `K` is a finite field
- `q` is notation for the cardinality of `K`
- `σ` is the indexing type for the variables of a multivariate polynomial ring over `K`

-/


universe u v

open BigOperators

section FiniteField

open MvPolynomial

open Function hiding eval

open Finset FiniteField

variable {K : Type _} {σ : Type _} [Fintype K] [Field K] [Fintype σ]

-- mathport name: exprq
local notation "q" => Fintype.card K

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `MvPolynomial.sum_mv_polynomial_eq_zero [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DecidableEq [`σ]) "]")
        (Term.explicitBinder "(" [`f] [":" (Term.app `MvPolynomial [`σ `K])] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (Term.proj `f "." `totalDegree)
           "<"
           («term_*_»
            («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
            "*"
            (Term.app `Fintype.card [`σ])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app `eval [`x `f]))
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" (Term.app `DecidableEq [`K]))]
              ":="
              (Term.app `Classical.decEq [`K]))))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
               ", "
               (Term.app `eval [`x `f]))
              "="
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder
                 (Lean.binderIdent `x)
                 [(group ":" (Term.arrow `σ "→" `K))]))
               ", "
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `d) []))
                " in "
                `f.support
                ", "
                («term_*_»
                 (Term.app `f.coeff [`d])
                 "*"
                 (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                  "∏"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  ", "
                  («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))))
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
                  ["[" [(Tactic.simpLemma [] [] `eval_eq')] "]"]
                  [])]))))
            [(calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `d) []))
                " in "
                `f.support
                ", "
                (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder
                   (Lean.binderIdent `x)
                   [(group ":" (Term.arrow `σ "→" `K))]))
                 ", "
                 («term_*_»
                  (Term.app `f.coeff [`d])
                  "*"
                  (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                   "∏"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                   ", "
                   («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))))
              ":="
              `sum_comm)
             (calcStep
              («term_=_» (Term.hole "_") "=" (num "0"))
              ":="
              (Term.app `sum_eq_zero [(Term.hole "_")]))])
           []
           (Tactic.intro "intro" [`d `hd])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hi)])
                  [])]
                "⟩")])]
            [":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              ","
              («term_<_»
               (Term.app `d [`i])
               "<"
               («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))]
            [])
           ";"
           (Tactic.exact
            "exact"
            (Term.app
             `f.exists_degree_lt
             [(«term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1")) `h `hd]))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder
                 (Lean.binderIdent `x)
                 [(group ":" (Term.arrow `σ "→" `K))]))
               ", "
               («term_*_»
                (Term.app `f.coeff [`d])
                "*"
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                 ", "
                 («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))
              "="
              («term_*_»
               (Term.app `f.coeff [`d])
               "*"
               (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `x)
                  [(group ":" (Term.arrow `σ "→" `K))]))
                ", "
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                 ", "
                 («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))))
             ":="
             `mul_sum.symm)
            [(calcStep
              («term_=_» (Term.hole "_") "=" (num "0"))
              ":="
              (Term.app («term_∘_» `mul_eq_zero.mpr "∘" `Or.inr) [(Term.hole "_")]))])
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder
                 (Lean.binderIdent `x)
                 [(group ":" (Term.arrow `σ "→" `K))]))
               ", "
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                ", "
                («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))
              "="
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinderCollection
                 [(Std.ExtendedBinder.extBinderParenthesized
                   "("
                   (Std.ExtendedBinder.extBinder
                    (Lean.binderIdent `x₀)
                    [(group
                      ":"
                      (Term.arrow
                       («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")
                       "→"
                       `K))])
                   ")")
                  (Std.ExtendedBinder.extBinderParenthesized
                   "("
                   (Std.ExtendedBinder.extBinder
                    (Lean.binderIdent `x)
                    [(group
                      ":"
                      («term{_:_//_}»
                       "{"
                       `x
                       [":" (Term.arrow `σ "→" `K)]
                       "//"
                       («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
                       "}"))])
                   ")")]))
               ", "
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                ", "
                («term_^_»
                 (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
                 "^"
                 (Term.app `d [`j])))))
             ":="
             (Term.proj
              (Term.app `Fintype.sum_fiberwise [(Term.hole "_") (Term.hole "_")])
              "."
              `symm))
            [(calcStep
              («term_=_» (Term.hole "_") "=" (num "0"))
              ":="
              (Term.app `Fintype.sum_eq_zero [(Term.hole "_") (Term.hole "_")]))])
           []
           (Tactic.intro "intro" [`x₀])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `e
              []
              [(Term.typeSpec
                ":"
                (Logic.Equiv.Defs.«term_≃_»
                 `K
                 " ≃ "
                 («term{_:_//_}» "{" `x [] "//" («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀) "}")))]
              ":="
              (Term.proj (Term.app `Equiv.subtypeEquivCodomain [(Term.hole "_")]) "." `symm))))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder
                 (Lean.binderIdent `x)
                 [(group
                   ":"
                   («term{_:_//_}»
                    "{"
                    `x
                    [":" (Term.arrow `σ "→" `K)]
                    "//"
                    («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
                    "}"))]))
               ", "
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                ", "
                («term_^_»
                 (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
                 "^"
                 (Term.app `d [`j]))))
              "="
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
               ", "
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
                ", "
                («term_^_»
                 (Term.app
                  (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                  [`j])
                 "^"
                 (Term.app `d [`j])))))
             ":="
             (Term.proj (Term.app `e.sum_comp [(Term.hole "_")]) "." `symm))
            [(calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
                ", "
                («term_*_»
                 (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                  "∏"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                  ", "
                  («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
                 "*"
                 («term_^_» `a "^" (Term.app `d [`i])))))
              ":="
              (Term.app `Fintype.sum_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_*_»
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                 ", "
                 («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
                "*"
                (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
                 ", "
                 («term_^_» `a "^" (Term.app `d [`i])))))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_sum)] "]")
                   [])]))))
             (calcStep
              («term_=_» (Term.hole "_") "=" (num "0"))
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
                    [(Tactic.rwRule [] (Term.app `sum_pow_lt_card_sub_one [(Term.hole "_") `hi]))
                     ","
                     (Tactic.rwRule [] `mul_zero)]
                    "]")
                   [])]))))])
           []
           (Tactic.intro "intro" [`a])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `e'
              []
              [(Term.typeSpec
                ":"
                (Logic.Equiv.Defs.«term_≃_»
                 (Term.app
                  `Sum
                  [(«term{_:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")
                   («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")])
                 " ≃ "
                 `σ))]
              ":="
              (Term.app `Equiv.sumCompl [(Term.hole "_")]))))
           []
           (Std.Tactic.tacticLetI_
            "letI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app `Unique [(«term{_:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")]))]
              ":="
              (Term.structInst
               "{"
               []
               [(Term.structInstField
                 (Term.structInstLVal `default [])
                 ":="
                 (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩"))
                []
                (Term.structInstField
                 (Term.structInstLVal `uniq [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.anonymousCtor "⟨" [`j "," `h] "⟩")]
                   []
                   "=>"
                   (Term.app `Subtype.val_injective [`h]))))]
               (Term.optEllipsis [])
               []
               "}"))))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
               ", "
               («term_^_»
                (Term.app
                 (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                 [`j])
                "^"
                (Term.app `d [`j])))
              "="
              («term_*_»
               («term_^_»
                (Term.app
                 (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                 [`i])
                "^"
                (Term.app `d [`i]))
               "*"
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `j)
                  [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
                ", "
                («term_^_»
                 (Term.app
                  (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                  [`j])
                 "^"
                 (Term.app `d [`j])))))
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `e'.prod_comp)
                    ","
                    (Tactic.rwRule [] `Fintype.prod_sum_type)
                    ","
                    (Tactic.rwRule [] `univ_unique)
                    ","
                    (Tactic.rwRule [] `prod_singleton)]
                   "]")
                  [])
                 []
                 (Tactic.tacticRfl "rfl")]))))
            [(calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_*_»
                («term_^_» `a "^" (Term.app `d [`i]))
                "*"
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder
                   (Lean.binderIdent `j)
                   [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
                 ", "
                 («term_^_»
                  (Term.app
                   (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                   [`j])
                  "^"
                  (Term.app `d [`j])))))
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
                    [(Tactic.rwRule [] `Equiv.subtypeEquivCodomain_symm_apply_eq)]
                    "]")
                   [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_*_»
                («term_^_» `a "^" (Term.app `d [`i]))
                "*"
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                 ", "
                 («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))))
              ":="
              (Term.app
               `congr_arg
               [(Term.hole "_")
                (Term.app `Fintype.prod_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_*_»
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                 ", "
                 («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
                "*"
                («term_^_» `a "^" (Term.app `d [`i]))))
              ":="
              (Term.app `mul_comm [(Term.hole "_") (Term.hole "_")]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hj)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.tacticShow_
              "show"
              («term_=_»
               («term_^_»
                (Term.app
                 (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                 [`j])
                "^"
                (Term.app `d [`j]))
               "="
               («term_^_»
                (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
                "^"
                (Term.app `d [`j]))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Equiv.subtypeEquivCodomain_symm_apply_ne)]
               "]")
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
         [(Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `DecidableEq [`K]))]
             ":="
             (Term.app `Classical.decEq [`K]))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
              ", "
              (Term.app `eval [`x `f]))
             "="
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `x)
                [(group ":" (Term.arrow `σ "→" `K))]))
              ", "
              (BigOperators.Algebra.BigOperators.Basic.finset.sum
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `d) []))
               " in "
               `f.support
               ", "
               («term_*_»
                (Term.app `f.coeff [`d])
                "*"
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                 ", "
                 («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))))
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
                 ["[" [(Tactic.simpLemma [] [] `eval_eq')] "]"]
                 [])]))))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (BigOperators.Algebra.BigOperators.Basic.finset.sum
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `d) []))
               " in "
               `f.support
               ", "
               (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `x)
                  [(group ":" (Term.arrow `σ "→" `K))]))
                ", "
                («term_*_»
                 (Term.app `f.coeff [`d])
                 "*"
                 (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                  "∏"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  ", "
                  («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))))
             ":="
             `sum_comm)
            (calcStep
             («term_=_» (Term.hole "_") "=" (num "0"))
             ":="
             (Term.app `sum_eq_zero [(Term.hole "_")]))])
          []
          (Tactic.intro "intro" [`d `hd])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hi)])
                 [])]
               "⟩")])]
           [":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ","
             («term_<_»
              (Term.app `d [`i])
              "<"
              («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))]
           [])
          ";"
          (Tactic.exact
           "exact"
           (Term.app
            `f.exists_degree_lt
            [(«term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1")) `h `hd]))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `x)
                [(group ":" (Term.arrow `σ "→" `K))]))
              ", "
              («term_*_»
               (Term.app `f.coeff [`d])
               "*"
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                ", "
                («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))
             "="
             («term_*_»
              (Term.app `f.coeff [`d])
              "*"
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder
                 (Lean.binderIdent `x)
                 [(group ":" (Term.arrow `σ "→" `K))]))
               ", "
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                ", "
                («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))))
            ":="
            `mul_sum.symm)
           [(calcStep
             («term_=_» (Term.hole "_") "=" (num "0"))
             ":="
             (Term.app («term_∘_» `mul_eq_zero.mpr "∘" `Or.inr) [(Term.hole "_")]))])
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `x)
                [(group ":" (Term.arrow `σ "→" `K))]))
              ", "
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               ", "
               («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))
             "="
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinderCollection
                [(Std.ExtendedBinder.extBinderParenthesized
                  "("
                  (Std.ExtendedBinder.extBinder
                   (Lean.binderIdent `x₀)
                   [(group
                     ":"
                     (Term.arrow
                      («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")
                      "→"
                      `K))])
                  ")")
                 (Std.ExtendedBinder.extBinderParenthesized
                  "("
                  (Std.ExtendedBinder.extBinder
                   (Lean.binderIdent `x)
                   [(group
                     ":"
                     («term{_:_//_}»
                      "{"
                      `x
                      [":" (Term.arrow `σ "→" `K)]
                      "//"
                      («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
                      "}"))])
                  ")")]))
              ", "
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
               ", "
               («term_^_»
                (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
                "^"
                (Term.app `d [`j])))))
            ":="
            (Term.proj
             (Term.app `Fintype.sum_fiberwise [(Term.hole "_") (Term.hole "_")])
             "."
             `symm))
           [(calcStep
             («term_=_» (Term.hole "_") "=" (num "0"))
             ":="
             (Term.app `Fintype.sum_eq_zero [(Term.hole "_") (Term.hole "_")]))])
          []
          (Tactic.intro "intro" [`x₀])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `e
             []
             [(Term.typeSpec
               ":"
               (Logic.Equiv.Defs.«term_≃_»
                `K
                " ≃ "
                («term{_:_//_}» "{" `x [] "//" («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀) "}")))]
             ":="
             (Term.proj (Term.app `Equiv.subtypeEquivCodomain [(Term.hole "_")]) "." `symm))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `x)
                [(group
                  ":"
                  («term{_:_//_}»
                   "{"
                   `x
                   [":" (Term.arrow `σ "→" `K)]
                   "//"
                   («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
                   "}"))]))
              ", "
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
               ", "
               («term_^_»
                (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
                "^"
                (Term.app `d [`j]))))
             "="
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
              ", "
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
               ", "
               («term_^_»
                (Term.app
                 (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                 [`j])
                "^"
                (Term.app `d [`j])))))
            ":="
            (Term.proj (Term.app `e.sum_comp [(Term.hole "_")]) "." `symm))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
               ", "
               («term_*_»
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                 ", "
                 («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
                "*"
                («term_^_» `a "^" (Term.app `d [`i])))))
             ":="
             (Term.app `Fintype.sum_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                ", "
                («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
               "*"
               (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
                ", "
                («term_^_» `a "^" (Term.app `d [`i])))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_sum)] "]")
                  [])]))))
            (calcStep
             («term_=_» (Term.hole "_") "=" (num "0"))
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
                   [(Tactic.rwRule [] (Term.app `sum_pow_lt_card_sub_one [(Term.hole "_") `hi]))
                    ","
                    (Tactic.rwRule [] `mul_zero)]
                   "]")
                  [])]))))])
          []
          (Tactic.intro "intro" [`a])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `e'
             []
             [(Term.typeSpec
               ":"
               (Logic.Equiv.Defs.«term_≃_»
                (Term.app
                 `Sum
                 [(«term{_:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")
                  («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")])
                " ≃ "
                `σ))]
             ":="
             (Term.app `Equiv.sumCompl [(Term.hole "_")]))))
          []
          (Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app `Unique [(«term{_:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")]))]
             ":="
             (Term.structInst
              "{"
              []
              [(Term.structInstField
                (Term.structInstLVal `default [])
                ":="
                (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩"))
               []
               (Term.structInstField
                (Term.structInstLVal `uniq [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.anonymousCtor "⟨" [`j "," `h] "⟩")]
                  []
                  "=>"
                  (Term.app `Subtype.val_injective [`h]))))]
              (Term.optEllipsis [])
              []
              "}"))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
              "∏"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
              ", "
              («term_^_»
               (Term.app
                (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                [`j])
               "^"
               (Term.app `d [`j])))
             "="
             («term_*_»
              («term_^_»
               (Term.app
                (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                [`i])
               "^"
               (Term.app `d [`i]))
              "*"
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder
                 (Lean.binderIdent `j)
                 [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
               ", "
               («term_^_»
                (Term.app
                 (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                 [`j])
                "^"
                (Term.app `d [`j])))))
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
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `e'.prod_comp)
                   ","
                   (Tactic.rwRule [] `Fintype.prod_sum_type)
                   ","
                   (Tactic.rwRule [] `univ_unique)
                   ","
                   (Tactic.rwRule [] `prod_singleton)]
                  "]")
                 [])
                []
                (Tactic.tacticRfl "rfl")]))))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               («term_^_» `a "^" (Term.app `d [`i]))
               "*"
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `j)
                  [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
                ", "
                («term_^_»
                 (Term.app
                  (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                  [`j])
                 "^"
                 (Term.app `d [`j])))))
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
                   [(Tactic.rwRule [] `Equiv.subtypeEquivCodomain_symm_apply_eq)]
                   "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               («term_^_» `a "^" (Term.app `d [`i]))
               "*"
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                ", "
                («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))))
             ":="
             (Term.app
              `congr_arg
              [(Term.hole "_")
               (Term.app `Fintype.prod_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                ", "
                («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
               "*"
               («term_^_» `a "^" (Term.app `d [`i]))))
             ":="
             (Term.app `mul_comm [(Term.hole "_") (Term.hole "_")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hj)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.tacticShow_
             "show"
             («term_=_»
              («term_^_»
               (Term.app
                (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
                [`j])
               "^"
               (Term.app `d [`j]))
              "="
              («term_^_»
               (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
               "^"
               (Term.app `d [`j]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Equiv.subtypeEquivCodomain_symm_apply_ne)]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hj)])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.tacticShow_
         "show"
         («term_=_»
          («term_^_»
           (Term.app
            (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
            [`j])
           "^"
           (Term.app `d [`j]))
          "="
          («term_^_»
           (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
           "^"
           (Term.app `d [`j]))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equiv.subtypeEquivCodomain_symm_apply_ne)] "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equiv.subtypeEquivCodomain_symm_apply_ne)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.subtypeEquivCodomain_symm_apply_ne
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticShow_
       "show"
       («term_=_»
        («term_^_»
         (Term.app
          (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
          [`j])
         "^"
         (Term.app `d [`j]))
        "="
        («term_^_»
         (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
         "^"
         (Term.app `d [`j]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_^_»
        (Term.app
         (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
         [`j])
        "^"
        (Term.app `d [`j]))
       "="
       («term_^_»
        (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
        "^"
        (Term.app `d [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")]) "^" (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`j "," `hj] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_»
       (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`j])
       "^"
       (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hj)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
          ", "
          («term_^_»
           (Term.app
            (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
            [`j])
           "^"
           (Term.app `d [`j])))
         "="
         («term_*_»
          («term_^_»
           (Term.app
            (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
            [`i])
           "^"
           (Term.app `d [`i]))
          "*"
          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
           "∏"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder
             (Lean.binderIdent `j)
             [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
           ", "
           («term_^_»
            (Term.app
             (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
             [`j])
            "^"
            (Term.app `d [`j])))))
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
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `e'.prod_comp)
               ","
               (Tactic.rwRule [] `Fintype.prod_sum_type)
               ","
               (Tactic.rwRule [] `univ_unique)
               ","
               (Tactic.rwRule [] `prod_singleton)]
              "]")
             [])
            []
            (Tactic.tacticRfl "rfl")]))))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           («term_^_» `a "^" (Term.app `d [`i]))
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `j)
              [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
            ", "
            («term_^_»
             (Term.app
              (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
              [`j])
             "^"
             (Term.app `d [`j])))))
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
               [(Tactic.rwRule [] `Equiv.subtypeEquivCodomain_symm_apply_eq)]
               "]")
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           («term_^_» `a "^" (Term.app `d [`i]))
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
            ", "
            («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))))
         ":="
         (Term.app
          `congr_arg
          [(Term.hole "_")
           (Term.app `Fintype.prod_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
            ", "
            («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
           "*"
           («term_^_» `a "^" (Term.app `d [`i]))))
         ":="
         (Term.app `mul_comm [(Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_comm [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
         ", "
         («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
        "*"
        («term_^_» `a "^" (Term.app `d [`i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
        ", "
        («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
       "*"
       («term_^_» `a "^" (Term.app `d [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `a "^" (Term.app `d [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
       ", "
       («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `x₀ [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
      "∏"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
      ", "
      («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app
       `congr_arg
       [(Term.hole "_")
        (Term.app `Fintype.prod_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fintype.prod_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.prod_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Fintype.prod_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        («term_^_» `a "^" (Term.app `d [`i]))
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
         ", "
         («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» `a "^" (Term.app `d [`i]))
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
        ", "
        («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
       ", "
       («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `x₀ [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `a "^" (Term.app `d [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equiv.subtypeEquivCodomain_symm_apply_eq)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equiv.subtypeEquivCodomain_symm_apply_eq)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.subtypeEquivCodomain_symm_apply_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        («term_^_» `a "^" (Term.app `d [`i]))
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder
           (Lean.binderIdent `j)
           [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
         ", "
         («term_^_»
          (Term.app
           (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
           [`j])
          "^"
          (Term.app `d [`j])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» `a "^" (Term.app `d [`i]))
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `j)
          [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
        ", "
        («term_^_»
         (Term.app
          (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
          [`j])
         "^"
         (Term.app `d [`j]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `j)
         [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
       ", "
       («term_^_»
        (Term.app
         (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
         [`j])
        "^"
        (Term.app `d [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`j])
       "^"
       (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `j "≠" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `a "^" (Term.app `d [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `e'.prod_comp)
             ","
             (Tactic.rwRule [] `Fintype.prod_sum_type)
             ","
             (Tactic.rwRule [] `univ_unique)
             ","
             (Tactic.rwRule [] `prod_singleton)]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `e'.prod_comp)
         ","
         (Tactic.rwRule [] `Fintype.prod_sum_type)
         ","
         (Tactic.rwRule [] `univ_unique)
         ","
         (Tactic.rwRule [] `prod_singleton)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `prod_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `univ_unique
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.prod_sum_type
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e'.prod_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
        ", "
        («term_^_»
         (Term.app
          (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
          [`j])
         "^"
         (Term.app `d [`j])))
       "="
       («term_*_»
        («term_^_»
         (Term.app
          (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
          [`i])
         "^"
         (Term.app `d [`i]))
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder
           (Lean.binderIdent `j)
           [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
         ", "
         («term_^_»
          (Term.app
           (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
           [`j])
          "^"
          (Term.app `d [`j])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_»
        (Term.app
         (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
         [`i])
        "^"
        (Term.app `d [`i]))
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `j)
          [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
        ", "
        («term_^_»
         (Term.app
          (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
          [`j])
         "^"
         (Term.app `d [`j]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `j)
         [(group ":" («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}"))]))
       ", "
       («term_^_»
        (Term.app
         (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
         [`j])
        "^"
        (Term.app `d [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`j])
       "^"
       (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `j "≠" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_»
       (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`i])
       "^"
       (Term.app `d [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
       ", "
       («term_^_»
        (Term.app
         (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
         [`j])
        "^"
        (Term.app `d [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`j])
       "^"
       (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
      "∏"
      (Std.ExtendedBinder.extBinders
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
      ", "
      («term_^_»
       (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`j])
       "^"
       (Term.app `d [`j])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticLetI_
       "letI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.app `Unique [(«term{_:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")]))]
         ":="
         (Term.structInst
          "{"
          []
          [(Term.structInstField
            (Term.structInstLVal `default [])
            ":="
            (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩"))
           []
           (Term.structInstField
            (Term.structInstLVal `uniq [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.anonymousCtor "⟨" [`j "," `h] "⟩")]
              []
              "=>"
              (Term.app `Subtype.val_injective [`h]))))]
          (Term.optEllipsis [])
          []
          "}"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `default [])
         ":="
         (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩"))
        []
        (Term.structInstField
         (Term.structInstLVal `uniq [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.anonymousCtor "⟨" [`j "," `h] "⟩")]
           []
           "=>"
           (Term.app `Subtype.val_injective [`h]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`j "," `h] "⟩")]
        []
        "=>"
        (Term.app `Subtype.val_injective [`h])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subtype.val_injective [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subtype.val_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`j "," `h] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Unique [(«term{_:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_:_//_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_:_//_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `j "=" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Unique
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `e'
         []
         [(Term.typeSpec
           ":"
           (Logic.Equiv.Defs.«term_≃_»
            (Term.app
             `Sum
             [(«term{_:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")
              («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")])
            " ≃ "
            `σ))]
         ":="
         (Term.app `Equiv.sumCompl [(Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Equiv.sumCompl [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Equiv.sumCompl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Logic.Equiv.Defs.«term_≃_»
       (Term.app
        `Sum
        [(«term{_:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")
         («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")])
       " ≃ "
       `σ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app
       `Sum
       [(«term{_:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")
        («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_:_//_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_:_//_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `j "≠" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_:_//_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_:_//_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term{_:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `j "=" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Sum
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`a])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group
              ":"
              («term{_:_//_}»
               "{"
               `x
               [":" (Term.arrow `σ "→" `K)]
               "//"
               («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
               "}"))]))
          ", "
          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
           "∏"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
           ", "
           («term_^_»
            (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
            "^"
            (Term.app `d [`j]))))
         "="
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
          ", "
          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
           "∏"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
           ", "
           («term_^_»
            (Term.app
             (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
             [`j])
            "^"
            (Term.app `d [`j])))))
        ":="
        (Term.proj (Term.app `e.sum_comp [(Term.hole "_")]) "." `symm))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
           "∑"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
           ", "
           («term_*_»
            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
             "∏"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
             ", "
             («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
            "*"
            («term_^_» `a "^" (Term.app `d [`i])))))
         ":="
         (Term.app `Fintype.sum_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
            ", "
            («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
            "∑"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
            ", "
            («term_^_» `a "^" (Term.app `d [`i])))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_sum)] "]") [])]))))
        (calcStep
         («term_=_» (Term.hole "_") "=" (num "0"))
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
               [(Tactic.rwRule [] (Term.app `sum_pow_lt_card_sub_one [(Term.hole "_") `hi]))
                ","
                (Tactic.rwRule [] `mul_zero)]
               "]")
              [])]))))])
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
            [(Tactic.rwRule [] (Term.app `sum_pow_lt_card_sub_one [(Term.hole "_") `hi]))
             ","
             (Tactic.rwRule [] `mul_zero)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `sum_pow_lt_card_sub_one [(Term.hole "_") `hi]))
         ","
         (Tactic.rwRule [] `mul_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sum_pow_lt_card_sub_one [(Term.hole "_") `hi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sum_pow_lt_card_sub_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_sum)] "]") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_sum)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
         ", "
         («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
         "∑"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
         ", "
         («term_^_» `a "^" (Term.app `d [`i])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
        ", "
        («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
        ", "
        («term_^_» `a "^" (Term.app `d [`i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
       ", "
       («term_^_» `a "^" (Term.app `d [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `a "^" (Term.app `d [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
       ", "
       («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `x₀ [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
      "∏"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
      ", "
      («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `Fintype.sum_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.sum_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
        ", "
        («term_*_»
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
          ", "
          («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
         "*"
         («term_^_» `a "^" (Term.app `d [`i])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
       ", "
       («term_*_»
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
         ", "
         («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
        "*"
        («term_^_» `a "^" (Term.app `d [`i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
        ", "
        («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
       "*"
       («term_^_» `a "^" (Term.app `d [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `a "^" (Term.app `d [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
       ", "
       («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `x₀ [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
      "∏"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
      ", "
      («term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.proj (Term.app `e.sum_comp [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `e.sum_comp [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e.sum_comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `e.sum_comp [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `x)
          [(group
            ":"
            («term{_:_//_}»
             "{"
             `x
             [":" (Term.arrow `σ "→" `K)]
             "//"
             («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
             "}"))]))
        ", "
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
         ", "
         («term_^_»
          (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
          "^"
          (Term.app `d [`j]))))
       "="
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
        ", "
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
         ", "
         («term_^_»
          (Term.app
           (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
           [`j])
          "^"
          (Term.app `d [`j])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `K)]))
       ", "
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
        ", "
        («term_^_»
         (Term.app
          (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
          [`j])
         "^"
         (Term.app `d [`j]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [(group ":" `σ)]))
       ", "
       («term_^_»
        (Term.app
         (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
         [`j])
        "^"
        (Term.app `d [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`j])
       "^"
       (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")") [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription "(" (Term.app `e [`a]) ":" [(Term.arrow `σ "→" `K)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `x)
         [(group
           ":"
           («term{_:_//_}»
            "{"
            `x
            [":" (Term.arrow `σ "→" `K)]
            "//"
            («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
            "}"))]))
       ", "
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
        ", "
        («term_^_»
         (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
         "^"
         (Term.app `d [`j]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
       ", "
       («term_^_»
        (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
        "^"
        (Term.app `d [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
       "^"
       (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}»
       "{"
       `x
       [":" (Term.arrow `σ "→" `K)]
       "//"
       («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_∘_» `x "∘" `coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 90, (some 90, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
      "∑"
      (Std.ExtendedBinder.extBinders
       (Std.ExtendedBinder.extBinder
        (Lean.binderIdent `x)
        [(group
          ":"
          («term{_:_//_}»
           "{"
           `x
           [":" (Term.arrow `σ "→" `K)]
           "//"
           («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
           "}"))]))
      ", "
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
       ", "
       («term_^_»
        (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
        "^"
        (Term.app `d [`j]))))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `e
         []
         [(Term.typeSpec
           ":"
           (Logic.Equiv.Defs.«term_≃_»
            `K
            " ≃ "
            («term{_:_//_}» "{" `x [] "//" («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀) "}")))]
         ":="
         (Term.proj (Term.app `Equiv.subtypeEquivCodomain [(Term.hole "_")]) "." `symm))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Equiv.subtypeEquivCodomain [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Equiv.subtypeEquivCodomain [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Equiv.subtypeEquivCodomain
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Equiv.subtypeEquivCodomain [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Logic.Equiv.Defs.«term_≃_»
       `K
       " ≃ "
       («term{_:_//_}» "{" `x [] "//" («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀) "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}» "{" `x [] "//" («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀) "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_∘_» `x "∘" `coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 90, (some 90, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x₀])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group ":" (Term.arrow `σ "→" `K))]))
          ", "
          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
           "∏"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           ", "
           («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))
         "="
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinderCollection
            [(Std.ExtendedBinder.extBinderParenthesized
              "("
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `x₀)
               [(group
                 ":"
                 (Term.arrow («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}") "→" `K))])
              ")")
             (Std.ExtendedBinder.extBinderParenthesized
              "("
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `x)
               [(group
                 ":"
                 («term{_:_//_}»
                  "{"
                  `x
                  [":" (Term.arrow `σ "→" `K)]
                  "//"
                  («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
                  "}"))])
              ")")]))
          ", "
          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
           "∏"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
           ", "
           («term_^_»
            (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
            "^"
            (Term.app `d [`j])))))
        ":="
        (Term.proj (Term.app `Fintype.sum_fiberwise [(Term.hole "_") (Term.hole "_")]) "." `symm))
       [(calcStep
         («term_=_» (Term.hole "_") "=" (num "0"))
         ":="
         (Term.app `Fintype.sum_eq_zero [(Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fintype.sum_eq_zero [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.sum_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.proj (Term.app `Fintype.sum_fiberwise [(Term.hole "_") (Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fintype.sum_fiberwise [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.sum_fiberwise
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Fintype.sum_fiberwise [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (Term.arrow `σ "→" `K))]))
        ", "
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))
       "="
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinderCollection
          [(Std.ExtendedBinder.extBinderParenthesized
            "("
            (Std.ExtendedBinder.extBinder
             (Lean.binderIdent `x₀)
             [(group
               ":"
               (Term.arrow («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}") "→" `K))])
            ")")
           (Std.ExtendedBinder.extBinderParenthesized
            "("
            (Std.ExtendedBinder.extBinder
             (Lean.binderIdent `x)
             [(group
               ":"
               («term{_:_//_}»
                "{"
                `x
                [":" (Term.arrow `σ "→" `K)]
                "//"
                («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
                "}"))])
            ")")]))
        ", "
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
         ", "
         («term_^_»
          (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
          "^"
          (Term.app `d [`j])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinderCollection
         [(Std.ExtendedBinder.extBinderParenthesized
           "("
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x₀)
            [(group
              ":"
              (Term.arrow («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}") "→" `K))])
           ")")
          (Std.ExtendedBinder.extBinderParenthesized
           "("
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group
              ":"
              («term{_:_//_}»
               "{"
               `x
               [":" (Term.arrow `σ "→" `K)]
               "//"
               («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
               "}"))])
           ")")]))
       ", "
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
        ", "
        («term_^_»
         (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
         "^"
         (Term.app `d [`j]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
       ", "
       («term_^_»
        (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
        "^"
        (Term.app `d [`j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
       "^"
       (Term.app `d [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")") [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription "(" `x ":" [(Term.arrow `σ "→" `K)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.ExtendedBinder.extBinderCollection', expected 'Std.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}»
       "{"
       `x
       [":" (Term.arrow `σ "→" `K)]
       "//"
       («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» («term_∘_» `x "∘" `coe) "=" `x₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_∘_» `x "∘" `coe)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 90, (some 90, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}") "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term{_:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `j "≠" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (Term.arrow `σ "→" `K))]))
       ", "
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `x [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
      "∑"
      (Std.ExtendedBinder.extBinders
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (Term.arrow `σ "→" `K))]))
      ", "
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group ":" (Term.arrow `σ "→" `K))]))
          ", "
          («term_*_»
           (Term.app `f.coeff [`d])
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
            ", "
            («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))
         "="
         («term_*_»
          (Term.app `f.coeff [`d])
          "*"
          (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
           "∑"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder
             (Lean.binderIdent `x)
             [(group ":" (Term.arrow `σ "→" `K))]))
           ", "
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
            ", "
            («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))))
        ":="
        `mul_sum.symm)
       [(calcStep
         («term_=_» (Term.hole "_") "=" (num "0"))
         ":="
         (Term.app («term_∘_» `mul_eq_zero.mpr "∘" `Or.inr) [(Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app («term_∘_» `mul_eq_zero.mpr "∘" `Or.inr) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      («term_∘_» `mul_eq_zero.mpr "∘" `Or.inr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Or.inr
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `mul_eq_zero.mpr
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 90, (some 90, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_∘_» `mul_eq_zero.mpr "∘" `Or.inr)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      `mul_sum.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (Term.arrow `σ "→" `K))]))
        ", "
        («term_*_»
         (Term.app `f.coeff [`d])
         "*"
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))
       "="
       («term_*_»
        (Term.app `f.coeff [`d])
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
         "∑"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (Term.arrow `σ "→" `K))]))
         ", "
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `f.coeff [`d])
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (Term.arrow `σ "→" `K))]))
        ", "
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (Term.arrow `σ "→" `K))]))
       ", "
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `x [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `f.coeff [`d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (Term.arrow `σ "→" `K))]))
       ", "
       («term_*_»
        (Term.app `f.coeff [`d])
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `f.coeff [`d])
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `x [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `f.coeff [`d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.coeff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
      "∑"
      (Std.ExtendedBinder.extBinders
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" (Term.arrow `σ "→" `K))]))
      ", "
      («term_*_»
       (Term.app `f.coeff [`d])
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        («term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `f.exists_degree_lt
        [(«term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1")) `h `hd]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `f.exists_degree_lt
       [(«term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1")) `h `hd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (FieldTheory.ChevalleyWarning.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.ChevalleyWarning.termq', expected 'FieldTheory.ChevalleyWarning.termq._@.FieldTheory.ChevalleyWarning._hyg.9'
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
  MvPolynomial.sum_mv_polynomial_eq_zero
  [ DecidableEq σ ] ( f : MvPolynomial σ K ) ( h : f . totalDegree < q - 1 * Fintype.card σ )
    : ∑ x , eval x f = 0
  :=
    by
      haveI : DecidableEq K := Classical.decEq K
        calc
          ∑ x , eval x f = ∑ x : σ → K , ∑ d in f.support , f.coeff d * ∏ i , x i ^ d i
            :=
            by simp only [ eval_eq' ]
          _ = ∑ d in f.support , ∑ x : σ → K , f.coeff d * ∏ i , x i ^ d i := sum_comm
            _ = 0 := sum_eq_zero _
        intro d hd
        obtain ⟨ i , hi ⟩ : ∃ i , d i < q - 1
        ;
        exact f.exists_degree_lt q - 1 h hd
        calc
          ∑ x : σ → K , f.coeff d * ∏ i , x i ^ d i = f.coeff d * ∑ x : σ → K , ∏ i , x i ^ d i
            :=
            mul_sum.symm
          _ = 0 := mul_eq_zero.mpr ∘ Or.inr _
        calc
          ∑ x : σ → K , ∏ i , x i ^ d i
              =
              ∑
                ( x₀ : { j // j ≠ i } → K ) ( x : { x : σ → K // x ∘ coe = x₀ } )
                ,
                ∏ j , ( x : σ → K ) j ^ d j
            :=
            Fintype.sum_fiberwise _ _ . symm
          _ = 0 := Fintype.sum_eq_zero _ _
        intro x₀
        let e : K ≃ { x // x ∘ coe = x₀ } := Equiv.subtypeEquivCodomain _ . symm
        calc
          ∑ x : { x : σ → K // x ∘ coe = x₀ } , ∏ j , ( x : σ → K ) j ^ d j
              =
              ∑ a : K , ∏ j : σ , ( e a : σ → K ) j ^ d j
            :=
            e.sum_comp _ . symm
          _ = ∑ a : K , ∏ j , x₀ j ^ d j * a ^ d i := Fintype.sum_congr _ _ _
            _ = ∏ j , x₀ j ^ d j * ∑ a : K , a ^ d i := by rw [ mul_sum ]
            _ = 0 := by rw [ sum_pow_lt_card_sub_one _ hi , mul_zero ]
        intro a
        let e' : Sum { j // j = i } { j // j ≠ i } ≃ σ := Equiv.sumCompl _
        letI
          : Unique { j // j = i }
            :=
            { default := ⟨ i , rfl ⟩ uniq := fun ⟨ j , h ⟩ => Subtype.val_injective h }
        calc
          ∏ j : σ , ( e a : σ → K ) j ^ d j
              =
              ( e a : σ → K ) i ^ d i * ∏ j : { j // j ≠ i } , ( e a : σ → K ) j ^ d j
            :=
            by rw [ ← e'.prod_comp , Fintype.prod_sum_type , univ_unique , prod_singleton ] rfl
          _ = a ^ d i * ∏ j : { j // j ≠ i } , ( e a : σ → K ) j ^ d j
              :=
              by rw [ Equiv.subtypeEquivCodomain_symm_apply_eq ]
            _ = a ^ d i * ∏ j , x₀ j ^ d j := congr_arg _ Fintype.prod_congr _ _ _
            _ = ∏ j , x₀ j ^ d j * a ^ d i := mul_comm _ _
        ·
          rintro ⟨ j , hj ⟩
            show ( e a : σ → K ) j ^ d j = x₀ ⟨ j , hj ⟩ ^ d j
            rw [ Equiv.subtypeEquivCodomain_symm_apply_ne ]
#align mv_polynomial.sum_mv_polynomial_eq_zero MvPolynomial.sum_mv_polynomial_eq_zero

variable [DecidableEq K] [DecidableEq σ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The Chevalley–Warning theorem.\nLet `(f i)` be a finite family of multivariate polynomials\nin finitely many variables (`X s`, `s : σ`) over a finite field of characteristic `p`.\nAssume that the sum of the total degrees of the `f i` is less than the cardinality of `σ`.\nThen the number of common solutions of the `f i` is divisible by `p`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `char_dvd_card_solutions_family [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p] [":" (termℕ "ℕ")] [] ")")
        (Term.instBinder "[" [] (Term.app `CharP [`K `p]) "]")
        (Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.implicitBinder "{" [`s] [":" (Term.app `Finset [`ι])] "}")
        (Term.implicitBinder
         "{"
         [`f]
         [":" (Term.arrow `ι "→" (Term.app `MvPolynomial [`σ `K]))]
         "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (BigOperators.Algebra.BigOperators.Basic.finset.sum
            "∑"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
            " in "
            `s
            ", "
            (Term.proj (Term.app `f [`i]) "." `totalDegree))
           "<"
           (Term.app `Fintype.card [`σ]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∣_»
         `p
         "∣"
         (Term.app
          `Fintype.card
          [(«term{_:_//_}»
            "{"
            `x
            [":" (Term.arrow `σ "→" `K)]
            "//"
            (Std.ExtendedBinder.«term∀__,_»
             "∀"
             (Lean.binderIdent `i)
             («binderTerm∈_» "∈" `s)
             ","
             («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (num "0")))
            "}")]))))
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
              [`hq []]
              [(Term.typeSpec
                ":"
                («term_<_»
                 (num "0")
                 "<"
                 («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))]
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
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_units)
                     ","
                     (Tactic.rwRule [] `Fintype.card_pos_iff)]
                    "]")
                   [])
                  []
                  (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(num "1")] "⟩"))]))))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `S
              []
              [(Term.typeSpec ":" (Term.app `Finset [(Term.arrow `σ "→" `K)]))]
              ":="
              (Set.«term{_|_}»
               "{"
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(«binderTerm∈_» "∈" `univ)])
               "|"
               (Std.ExtendedBinder.«term∀__,_»
                "∀"
                (Lean.binderIdent `i)
                («binderTerm∈_» "∈" `s)
                ","
                («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (num "0")))
               "}"))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hS []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`x]
                 [(Term.typeSpec ":" (Term.arrow `σ "→" `K))]
                 ","
                 («term_↔_»
                  («term_∈_» `x "∈" `S)
                  "↔"
                  (Term.forall
                   "∀"
                   [`i]
                   [(Term.typeSpec ":" `ι)]
                   ","
                   (Term.arrow
                    («term_∈_» `i "∈" `s)
                    "→"
                    («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (num "0")))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`x])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `S)
                     ","
                     (Tactic.simpLemma [] [] `true_and_iff)
                     ","
                     (Tactic.simpLemma [] [] `sep_def)
                     ","
                     (Tactic.simpLemma [] [] `mem_filter)
                     ","
                     (Tactic.simpLemma [] [] `mem_univ)]
                    "]"]
                   [])]))))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `F
              []
              [(Term.typeSpec ":" (Term.app `MvPolynomial [`σ `K]))]
              ":="
              (BigOperators.Algebra.BigOperators.Basic.finset.prod
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               " in "
               `s
               ", "
               («term_-_»
                (num "1")
                "-"
                («term_^_»
                 (Term.app `f [`i])
                 "^"
                 («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hF []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`x]
                 []
                 ","
                 («term_=_»
                  (Term.app `eval [`x `F])
                  "="
                  (termIfThenElse "if" («term_∈_» `x "∈" `S) "then" (num "1") "else" (num "0")))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`x])
                  []
                  (calcTactic
                   "calc"
                   (calcStep
                    («term_=_»
                     (Term.app `eval [`x `F])
                     "="
                     (BigOperators.Algebra.BigOperators.Basic.finset.prod
                      "∏"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                      " in "
                      `s
                      ", "
                      (Term.app
                       `eval
                       [`x
                        («term_-_»
                         (num "1")
                         "-"
                         («term_^_»
                          (Term.app `f [`i])
                          "^"
                          («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))])))
                    ":="
                    (Term.app `eval_prod [`s (Term.hole "_") `x]))
                   [(calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      (termIfThenElse "if" («term_∈_» `x "∈" `S) "then" (num "1") "else" (num "0")))
                     ":="
                     (Term.hole "_"))])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] (Term.proj (Term.app `eval [`x]) "." `map_sub))
                     ","
                     (Tactic.simpLemma [] [] (Term.proj (Term.app `eval [`x]) "." `map_pow))
                     ","
                     (Tactic.simpLemma [] [] (Term.proj (Term.app `eval [`x]) "." `map_one))]
                    "]"]
                   [])
                  []
                  (Mathlib.Tactic.splitIfs
                   "split_ifs"
                   []
                   ["with" [(Lean.binderIdent `hx) (Lean.binderIdent `hx)]])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.apply "apply" `Finset.prod_eq_one)
                    []
                    (Tactic.intro "intro" [`i `hi])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hS)] "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] (Term.app `hx [`i `hi]))
                       ","
                       (Tactic.rwRule [] (Term.app `zero_pow [`hq]))
                       ","
                       (Tactic.rwRule [] `sub_zero)]
                      "]")
                     [])])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Std.Tactic.obtain
                     "obtain"
                     [(Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hi)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                           [])]
                         "⟩")])]
                     [":"
                      («term∃_,_»
                       "∃"
                       (Lean.explicitBinders
                        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
                       ","
                       («term_∧_»
                        («term_∈_» `i "∈" `s)
                        "∧"
                        («term_≠_» (Term.app `eval [`x (Term.app `f [`i])]) "≠" (num "0"))))]
                     [":="
                      [(Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Std.Tactic.Simpa.simpa
                            "simpa"
                            []
                            []
                            (Std.Tactic.Simpa.simpaArgsRest
                             []
                             []
                             ["only"]
                             [(Tactic.simpArgs
                               "["
                               [(Tactic.simpLemma [] [] `hS)
                                ","
                                (Tactic.simpLemma [] [] `not_forall)
                                ","
                                (Tactic.simpLemma [] [] `not_imp)]
                               "]")]
                             ["using" `hx]))])))]])
                    []
                    (Tactic.apply "apply" (Term.app `Finset.prod_eq_zero [`hi]))
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        []
                        (Term.app
                         `pow_card_sub_one_eq_one
                         [(Term.app `eval [`x (Term.app `f [`i])]) `hx]))
                       ","
                       (Tactic.rwRule [] `sub_self)]
                      "]")
                     [])])]))))))
           []
           (Mathlib.Tactic.tacticHave_
            "have"
            [`key []]
            [(Term.typeSpec
              ":"
              («term_=_»
               (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                ", "
                (Term.app `eval [`x `F]))
               "="
               (Term.app
                `Fintype.card
                [(«term{_:_//_}»
                  "{"
                  `x
                  [":" (Term.arrow `σ "→" `K)]
                  "//"
                  (Std.ExtendedBinder.«term∀__,_»
                   "∀"
                   (Lean.binderIdent `i)
                   («binderTerm∈_» "∈" `s)
                   ","
                   («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (num "0")))
                  "}")])))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `Fintype.card_of_subtype [`S `hS]))
              ","
              (Tactic.rwRule [] `card_eq_sum_ones)
              ","
              (Tactic.rwRule [] `Nat.cast_sum)
              ","
              (Tactic.rwRule [] `Nat.cast_one)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `Fintype.sum_extend_by_zero [`S]))
              ","
              (Tactic.rwRule
               []
               (Term.app
                `sum_congr
                [`rfl (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `hF [`x])))]))]
             "]")
            [])
           []
           (Tactic.tacticShow_
            "show"
            («term_∣_»
             `p
             "∣"
             (Term.app
              `Fintype.card
              [(«term{_:_//_}»
                "{"
                `x
                []
                "//"
                (Term.forall
                 "∀"
                 [`i]
                 [(Term.typeSpec ":" `ι)]
                 ","
                 (Term.arrow
                  («term_∈_» `i "∈" `s)
                  "→"
                  («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (num "0"))))
                "}")])))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `CharP.cast_eq_zero_iff [`K]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `key)]
             "]")
            [])
           []
           (Tactic.tacticShow_
            "show"
            («term_=_»
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
              ", "
              (Term.app `eval [`x `F]))
             "="
             (num "0")))
           []
           (Tactic.apply "apply" `F.sum_mv_polynomial_eq_zero)
           []
           (Tactic.tacticShow_
            "show"
            («term_<_»
             `F.total_degree
             "<"
             («term_*_»
              («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
              "*"
              (Term.app `Fintype.card [`σ]))))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_≤_»
              `F.total_degree
              "≤"
              (BigOperators.Algebra.BigOperators.Basic.finset.sum
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               " in "
               `s
               ", "
               (Term.proj
                («term_-_»
                 (num "1")
                 "-"
                 («term_^_»
                  (Term.app `f [`i])
                  "^"
                  («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))
                "."
                `totalDegree)))
             ":="
             (Term.app `total_degree_finset_prod [`s (Term.hole "_")]))
            [(calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                " in "
                `s
                ", "
                («term_*_»
                 («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
                 "*"
                 (Term.proj (Term.app `f [`i]) "." `totalDegree))))
              ":="
              (Term.app
               `sum_le_sum
               [(Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))]))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_*_»
                («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
                "*"
                (BigOperators.Algebra.BigOperators.Basic.finset.sum
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                 " in "
                 `s
                 ", "
                 (Term.proj (Term.app `f [`i]) "." `totalDegree))))
              ":="
              `mul_sum.symm)
             (calcStep
              («term_<_»
               (Term.hole "_")
               "<"
               («term_*_»
                («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
                "*"
                (Term.app `Fintype.card [`σ])))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.tacticRwa__
                   "rwa"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mul_lt_mul_left [`hq]))] "]")
                   [])]))))])
           []
           (Tactic.tacticShow_
            "show"
            («term_≤_»
             (Term.proj
              («term_-_»
               (num "1")
               "-"
               («term_^_»
                (Term.app `f [`i])
                "^"
                («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))
              "."
              `totalDegree)
             "≤"
             («term_*_»
              («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
              "*"
              (Term.proj (Term.app `f [`i]) "." `totalDegree))))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_≤_»
              (Term.proj
               («term_-_»
                (num "1")
                "-"
                («term_^_»
                 (Term.app `f [`i])
                 "^"
                 («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))
               "."
               `totalDegree)
              "≤"
              (Term.app
               `max
               [(Term.proj
                 (Term.typeAscription "(" (num "1") ":" [(Term.app `MvPolynomial [`σ `K])] ")")
                 "."
                 `totalDegree)
                (Term.proj
                 («term_^_»
                  (Term.app `f [`i])
                  "^"
                  («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1")))
                 "."
                 `totalDegree)]))
             ":="
             (Term.app `total_degree_sub [(Term.hole "_") (Term.hole "_")]))
            [(calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               (Term.proj
                («term_^_»
                 (Term.app `f [`i])
                 "^"
                 («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1")))
                "."
                `totalDegree))
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
                    [(Tactic.simpLemma [] [] `max_eq_right)
                     ","
                     (Tactic.simpLemma [] [] `Nat.zero_le)
                     ","
                     (Tactic.simpLemma [] [] `total_degree_one)]
                    "]"]
                   [])]))))
             (calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_*_»
                («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
                "*"
                (Term.proj (Term.app `f [`i]) "." `totalDegree)))
              ":="
              (Term.app `total_degree_pow [(Term.hole "_") (Term.hole "_")]))])])))
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
             [`hq []]
             [(Term.typeSpec
               ":"
               («term_<_»
                (num "0")
                "<"
                («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))]
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_units)
                    ","
                    (Tactic.rwRule [] `Fintype.card_pos_iff)]
                   "]")
                  [])
                 []
                 (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(num "1")] "⟩"))]))))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `S
             []
             [(Term.typeSpec ":" (Term.app `Finset [(Term.arrow `σ "→" `K)]))]
             ":="
             (Set.«term{_|_}»
              "{"
              (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(«binderTerm∈_» "∈" `univ)])
              "|"
              (Std.ExtendedBinder.«term∀__,_»
               "∀"
               (Lean.binderIdent `i)
               («binderTerm∈_» "∈" `s)
               ","
               («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (num "0")))
              "}"))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hS []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`x]
                [(Term.typeSpec ":" (Term.arrow `σ "→" `K))]
                ","
                («term_↔_»
                 («term_∈_» `x "∈" `S)
                 "↔"
                 (Term.forall
                  "∀"
                  [`i]
                  [(Term.typeSpec ":" `ι)]
                  ","
                  (Term.arrow
                   («term_∈_» `i "∈" `s)
                   "→"
                   («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (num "0")))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`x])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `S)
                    ","
                    (Tactic.simpLemma [] [] `true_and_iff)
                    ","
                    (Tactic.simpLemma [] [] `sep_def)
                    ","
                    (Tactic.simpLemma [] [] `mem_filter)
                    ","
                    (Tactic.simpLemma [] [] `mem_univ)]
                   "]"]
                  [])]))))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `F
             []
             [(Term.typeSpec ":" (Term.app `MvPolynomial [`σ `K]))]
             ":="
             (BigOperators.Algebra.BigOperators.Basic.finset.prod
              "∏"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              " in "
              `s
              ", "
              («term_-_»
               (num "1")
               "-"
               («term_^_»
                (Term.app `f [`i])
                "^"
                («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hF []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`x]
                []
                ","
                («term_=_»
                 (Term.app `eval [`x `F])
                 "="
                 (termIfThenElse "if" («term_∈_» `x "∈" `S) "then" (num "1") "else" (num "0")))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`x])
                 []
                 (calcTactic
                  "calc"
                  (calcStep
                   («term_=_»
                    (Term.app `eval [`x `F])
                    "="
                    (BigOperators.Algebra.BigOperators.Basic.finset.prod
                     "∏"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     " in "
                     `s
                     ", "
                     (Term.app
                      `eval
                      [`x
                       («term_-_»
                        (num "1")
                        "-"
                        («term_^_»
                         (Term.app `f [`i])
                         "^"
                         («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))])))
                   ":="
                   (Term.app `eval_prod [`s (Term.hole "_") `x]))
                  [(calcStep
                    («term_=_»
                     (Term.hole "_")
                     "="
                     (termIfThenElse "if" («term_∈_» `x "∈" `S) "then" (num "1") "else" (num "0")))
                    ":="
                    (Term.hole "_"))])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] (Term.proj (Term.app `eval [`x]) "." `map_sub))
                    ","
                    (Tactic.simpLemma [] [] (Term.proj (Term.app `eval [`x]) "." `map_pow))
                    ","
                    (Tactic.simpLemma [] [] (Term.proj (Term.app `eval [`x]) "." `map_one))]
                   "]"]
                  [])
                 []
                 (Mathlib.Tactic.splitIfs
                  "split_ifs"
                  []
                  ["with" [(Lean.binderIdent `hx) (Lean.binderIdent `hx)]])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.apply "apply" `Finset.prod_eq_one)
                   []
                   (Tactic.intro "intro" [`i `hi])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hS)] "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] (Term.app `hx [`i `hi]))
                      ","
                      (Tactic.rwRule [] (Term.app `zero_pow [`hq]))
                      ","
                      (Tactic.rwRule [] `sub_zero)]
                     "]")
                    [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Std.Tactic.obtain
                    "obtain"
                    [(Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hi)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                          [])]
                        "⟩")])]
                    [":"
                     («term∃_,_»
                      "∃"
                      (Lean.explicitBinders
                       (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
                      ","
                      («term_∧_»
                       («term_∈_» `i "∈" `s)
                       "∧"
                       («term_≠_» (Term.app `eval [`x (Term.app `f [`i])]) "≠" (num "0"))))]
                    [":="
                     [(Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Std.Tactic.Simpa.simpa
                           "simpa"
                           []
                           []
                           (Std.Tactic.Simpa.simpaArgsRest
                            []
                            []
                            ["only"]
                            [(Tactic.simpArgs
                              "["
                              [(Tactic.simpLemma [] [] `hS)
                               ","
                               (Tactic.simpLemma [] [] `not_forall)
                               ","
                               (Tactic.simpLemma [] [] `not_imp)]
                              "]")]
                            ["using" `hx]))])))]])
                   []
                   (Tactic.apply "apply" (Term.app `Finset.prod_eq_zero [`hi]))
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       []
                       (Term.app
                        `pow_card_sub_one_eq_one
                        [(Term.app `eval [`x (Term.app `f [`i])]) `hx]))
                      ","
                      (Tactic.rwRule [] `sub_self)]
                     "]")
                    [])])]))))))
          []
          (Mathlib.Tactic.tacticHave_
           "have"
           [`key []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
               ", "
               (Term.app `eval [`x `F]))
              "="
              (Term.app
               `Fintype.card
               [(«term{_:_//_}»
                 "{"
                 `x
                 [":" (Term.arrow `σ "→" `K)]
                 "//"
                 (Std.ExtendedBinder.«term∀__,_»
                  "∀"
                  (Lean.binderIdent `i)
                  («binderTerm∈_» "∈" `s)
                  ","
                  («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (num "0")))
                 "}")])))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `Fintype.card_of_subtype [`S `hS]))
             ","
             (Tactic.rwRule [] `card_eq_sum_ones)
             ","
             (Tactic.rwRule [] `Nat.cast_sum)
             ","
             (Tactic.rwRule [] `Nat.cast_one)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `Fintype.sum_extend_by_zero [`S]))
             ","
             (Tactic.rwRule
              []
              (Term.app
               `sum_congr
               [`rfl (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.app `hF [`x])))]))]
            "]")
           [])
          []
          (Tactic.tacticShow_
           "show"
           («term_∣_»
            `p
            "∣"
            (Term.app
             `Fintype.card
             [(«term{_:_//_}»
               "{"
               `x
               []
               "//"
               (Term.forall
                "∀"
                [`i]
                [(Term.typeSpec ":" `ι)]
                ","
                (Term.arrow
                 («term_∈_» `i "∈" `s)
                 "→"
                 («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (num "0"))))
               "}")])))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `CharP.cast_eq_zero_iff [`K]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `key)]
            "]")
           [])
          []
          (Tactic.tacticShow_
           "show"
           («term_=_»
            (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
             "∑"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             ", "
             (Term.app `eval [`x `F]))
            "="
            (num "0")))
          []
          (Tactic.apply "apply" `F.sum_mv_polynomial_eq_zero)
          []
          (Tactic.tacticShow_
           "show"
           («term_<_»
            `F.total_degree
            "<"
            («term_*_»
             («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
             "*"
             (Term.app `Fintype.card [`σ]))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             `F.total_degree
             "≤"
             (BigOperators.Algebra.BigOperators.Basic.finset.sum
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              " in "
              `s
              ", "
              (Term.proj
               («term_-_»
                (num "1")
                "-"
                («term_^_»
                 (Term.app `f [`i])
                 "^"
                 («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))
               "."
               `totalDegree)))
            ":="
            (Term.app `total_degree_finset_prod [`s (Term.hole "_")]))
           [(calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              (BigOperators.Algebra.BigOperators.Basic.finset.sum
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               " in "
               `s
               ", "
               («term_*_»
                («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
                "*"
                (Term.proj (Term.app `f [`i]) "." `totalDegree))))
             ":="
             (Term.app
              `sum_le_sum
              [(Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))]))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
               "*"
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                " in "
                `s
                ", "
                (Term.proj (Term.app `f [`i]) "." `totalDegree))))
             ":="
             `mul_sum.symm)
            (calcStep
             («term_<_»
              (Term.hole "_")
              "<"
              («term_*_»
               («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
               "*"
               (Term.app `Fintype.card [`σ])))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mul_lt_mul_left [`hq]))] "]")
                  [])]))))])
          []
          (Tactic.tacticShow_
           "show"
           («term_≤_»
            (Term.proj
             («term_-_»
              (num "1")
              "-"
              («term_^_»
               (Term.app `f [`i])
               "^"
               («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))
             "."
             `totalDegree)
            "≤"
            («term_*_»
             («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
             "*"
             (Term.proj (Term.app `f [`i]) "." `totalDegree))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             (Term.proj
              («term_-_»
               (num "1")
               "-"
               («term_^_»
                (Term.app `f [`i])
                "^"
                («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))
              "."
              `totalDegree)
             "≤"
             (Term.app
              `max
              [(Term.proj
                (Term.typeAscription "(" (num "1") ":" [(Term.app `MvPolynomial [`σ `K])] ")")
                "."
                `totalDegree)
               (Term.proj
                («term_^_»
                 (Term.app `f [`i])
                 "^"
                 («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1")))
                "."
                `totalDegree)]))
            ":="
            (Term.app `total_degree_sub [(Term.hole "_") (Term.hole "_")]))
           [(calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              (Term.proj
               («term_^_»
                (Term.app `f [`i])
                "^"
                («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1")))
               "."
               `totalDegree))
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
                   [(Tactic.simpLemma [] [] `max_eq_right)
                    ","
                    (Tactic.simpLemma [] [] `Nat.zero_le)
                    ","
                    (Tactic.simpLemma [] [] `total_degree_one)]
                   "]"]
                  [])]))))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_*_»
               («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
               "*"
               (Term.proj (Term.app `f [`i]) "." `totalDegree)))
             ":="
             (Term.app `total_degree_pow [(Term.hole "_") (Term.hole "_")]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (Term.proj
          («term_-_»
           (num "1")
           "-"
           («term_^_»
            (Term.app `f [`i])
            "^"
            («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))))
          "."
          `totalDegree)
         "≤"
         (Term.app
          `max
          [(Term.proj
            (Term.typeAscription "(" (num "1") ":" [(Term.app `MvPolynomial [`σ `K])] ")")
            "."
            `totalDegree)
           (Term.proj
            («term_^_»
             (Term.app `f [`i])
             "^"
             («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1")))
            "."
            `totalDegree)]))
        ":="
        (Term.app `total_degree_sub [(Term.hole "_") (Term.hole "_")]))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          (Term.proj
           («term_^_»
            (Term.app `f [`i])
            "^"
            («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1")))
           "."
           `totalDegree))
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
               [(Tactic.simpLemma [] [] `max_eq_right)
                ","
                (Tactic.simpLemma [] [] `Nat.zero_le)
                ","
                (Tactic.simpLemma [] [] `total_degree_one)]
               "]"]
              [])]))))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
           "*"
           (Term.proj (Term.app `f [`i]) "." `totalDegree)))
         ":="
         (Term.app `total_degree_pow [(Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `total_degree_pow [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `total_degree_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_*_»
        («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
        "*"
        (Term.proj (Term.app `f [`i]) "." `totalDegree)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
       "*"
       (Term.proj (Term.app `f [`i]) "." `totalDegree))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `f [`i]) "." `totalDegree)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`i]) ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (FieldTheory.ChevalleyWarning.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.ChevalleyWarning.termq', expected 'FieldTheory.ChevalleyWarning.termq._@.FieldTheory.ChevalleyWarning._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The Chevalley–Warning theorem.
    Let `(f i)` be a finite family of multivariate polynomials
    in finitely many variables (`X s`, `s : σ`) over a finite field of characteristic `p`.
    Assume that the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
    Then the number of common solutions of the `f i` is divisible by `p`. -/
  theorem
    char_dvd_card_solutions_family
    ( p : ℕ )
        [ CharP K p ]
        { ι : Type _ }
        { s : Finset ι }
        { f : ι → MvPolynomial σ K }
        ( h : ∑ i in s , f i . totalDegree < Fintype.card σ )
      : p ∣ Fintype.card { x : σ → K // ∀ i ∈ s , eval x f i = 0 }
    :=
      by
        have hq : 0 < q - 1 := by rw [ ← Fintype.card_units , Fintype.card_pos_iff ] exact ⟨ 1 ⟩
          let S : Finset σ → K := { x ∈ univ | ∀ i ∈ s , eval x f i = 0 }
          have
            hS
              : ∀ x : σ → K , x ∈ S ↔ ∀ i : ι , i ∈ s → eval x f i = 0
              :=
              by intro x simp only [ S , true_and_iff , sep_def , mem_filter , mem_univ ]
          let F : MvPolynomial σ K := ∏ i in s , 1 - f i ^ q - 1
          have
            hF
              : ∀ x , eval x F = if x ∈ S then 1 else 0
              :=
              by
                intro x
                  calc
                    eval x F = ∏ i in s , eval x 1 - f i ^ q - 1 := eval_prod s _ x
                    _ = if x ∈ S then 1 else 0 := _
                  simp only [ eval x . map_sub , eval x . map_pow , eval x . map_one ]
                  split_ifs with hx hx
                  ·
                    apply Finset.prod_eq_one
                      intro i hi
                      rw [ hS ] at hx
                      rw [ hx i hi , zero_pow hq , sub_zero ]
                  ·
                    obtain
                        ⟨ i , hi , hx ⟩
                        : ∃ i : ι , i ∈ s ∧ eval x f i ≠ 0
                        := by simpa only [ hS , not_forall , not_imp ] using hx
                      apply Finset.prod_eq_zero hi
                      rw [ pow_card_sub_one_eq_one eval x f i hx , sub_self ]
          have key : ∑ x , eval x F = Fintype.card { x : σ → K // ∀ i ∈ s , eval x f i = 0 }
          rw
            [
              Fintype.card_of_subtype S hS
                ,
                card_eq_sum_ones
                ,
                Nat.cast_sum
                ,
                Nat.cast_one
                ,
                ← Fintype.sum_extend_by_zero S
                ,
                sum_congr rfl fun x hx => hF x
              ]
          show p ∣ Fintype.card { x // ∀ i : ι , i ∈ s → eval x f i = 0 }
          rw [ ← CharP.cast_eq_zero_iff K , ← key ]
          show ∑ x , eval x F = 0
          apply F.sum_mv_polynomial_eq_zero
          show F.total_degree < q - 1 * Fintype.card σ
          calc
            F.total_degree ≤ ∑ i in s , 1 - f i ^ q - 1 . totalDegree
              :=
              total_degree_finset_prod s _
            _ ≤ ∑ i in s , q - 1 * f i . totalDegree := sum_le_sum fun i hi => _
              _ = q - 1 * ∑ i in s , f i . totalDegree := mul_sum.symm
              _ < q - 1 * Fintype.card σ := by rwa [ mul_lt_mul_left hq ]
          show 1 - f i ^ q - 1 . totalDegree ≤ q - 1 * f i . totalDegree
          calc
            1 - f i ^ q - 1 . totalDegree
                ≤
                max ( 1 : MvPolynomial σ K ) . totalDegree f i ^ q - 1 . totalDegree
              :=
              total_degree_sub _ _
            _ ≤ f i ^ q - 1 . totalDegree
                :=
                by simp only [ max_eq_right , Nat.zero_le , total_degree_one ]
              _ ≤ q - 1 * f i . totalDegree := total_degree_pow _ _
#align char_dvd_card_solutions_family char_dvd_card_solutions_family

/-- The Chevalley–Warning theorem.
Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
over a finite field of characteristic `p`.
Assume that the total degree of `f` is less than the cardinality of `σ`.
Then the number of solutions of `f` is divisible by `p`.
See `char_dvd_card_solutions_family` for a version that takes a family of polynomials `f i`. -/
theorem char_dvd_card_solutions (p : ℕ) [CharP K p] {f : MvPolynomial σ K}
    (h : f.totalDegree < Fintype.card σ) : p ∣ Fintype.card { x : σ → K // eval x f = 0 } :=
  by
  let F : Unit → MvPolynomial σ K := fun _ => f
  have : (∑ i : Unit, (F i).totalDegree) < Fintype.card σ := by
    simpa only [Fintype.univ_punit, sum_singleton] using h
  have key := char_dvd_card_solutions_family p this
  simp only [F, Fintype.univ_punit, forall_eq, mem_singleton] at key
  convert key
#align char_dvd_card_solutions char_dvd_card_solutions

end FiniteField

