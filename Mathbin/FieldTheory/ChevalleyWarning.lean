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

open_locale BigOperators

section FiniteField

open MvPolynomial

open Function hiding eval

open Finset FiniteField

variable {K : Type _} {σ : Type _} [Fintype K] [Field K] [Fintype σ]

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
       `f.total_degree
       "<"
       (Finset.Data.Finset.Fold.«term_*_»
        («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
        "*"
        (Term.app `Fintype.card [`σ])))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
      ", "
      (Term.app `eval [`x `f]))
     "="
     (numLit "0"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" (Term.app `DecidableEq [`K]))]
           ":="
           (Term.app `Classical.decEq [`K]))))
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_»
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             ", "
             (Term.app `eval [`x `f]))
            "="
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.arrow `σ "→" `K)]))
             ", "
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
              " in "
              `f.support
              ", "
              (Finset.Data.Finset.Fold.«term_*_»
               (Term.app `f.coeff [`d])
               "*"
               (Algebra.BigOperators.Basic.«term∏_,_»
                "∏"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `eval_eq')] "]"] []) [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
             " in "
             `f.support
             ", "
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.arrow `σ "→" `K)]))
              ", "
              (Finset.Data.Finset.Fold.«term_*_»
               (Term.app `f.coeff [`d])
               "*"
               (Algebra.BigOperators.Basic.«term∏_,_»
                "∏"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))))
           ":="
           `sum_comm)
          (calcStep («term_=_» (Term.hole "_") "=" (numLit "0")) ":=" (Term.app `sum_eq_zero [(Term.hole "_")]))])
        [])
       (group (Tactic.intro "intro" [`d `hd]) [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hi)]) [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
           ","
           («term_<_» (Term.app `d [`i]) "<" («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))]
         [])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app `f.exists_degree_lt [(«term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")) `h `hd]))
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_»
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.arrow `σ "→" `K)]))
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.app `f.coeff [`d])
              "*"
              (Algebra.BigOperators.Basic.«term∏_,_»
               "∏"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
               ", "
               (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Term.app `f.coeff [`d])
             "*"
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.arrow `σ "→" `K)]))
              ", "
              (Algebra.BigOperators.Basic.«term∏_,_»
               "∏"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
               ", "
               (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))))
           ":="
           `mul_sum.symm)
          (calcStep
           («term_=_» (Term.hole "_") "=" (numLit "0"))
           ":="
           (Term.app («term_∘_» `mul_eq_zero.mpr "∘" `Or.inr) [(Term.hole "_")]))])
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_»
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.arrow `σ "→" `K)]))
             ", "
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))
            "="
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              [(Lean.bracketedExplicitBinders
                "("
                [(Lean.binderIdent `x₀)]
                ":"
                (Term.arrow («term{__:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}") "→" `K)
                ")")
               (Lean.bracketedExplicitBinders
                "("
                [(Lean.binderIdent `x)]
                ":"
                («term{__:_//_}»
                 "{"
                 `x
                 [":" (Term.arrow `σ "→" `K)]
                 "//"
                 («term_=_» («term_∘_» `x "∘" `coeₓ) "=" `x₀)
                 "}")
                ")")])
             ", "
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app (Term.paren "(" [`x [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
               "^"
               (Term.app `d [`j])))))
           ":="
           (Term.proj (Term.app `Fintype.sum_fiberwise [(Term.hole "_") (Term.hole "_")]) "." `symm))
          (calcStep
           («term_=_» (Term.hole "_") "=" (numLit "0"))
           ":="
           (Term.app `Fintype.sum_eq_zero [(Term.hole "_") (Term.hole "_")]))])
        [])
       (group (Tactic.intro "intro" [`x₀]) [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `e
           [(Term.typeSpec
             ":"
             (Data.Equiv.Basic.«term_≃_»
              `K
              " ≃ "
              («term{__:_//_}» "{" `x [] "//" («term_=_» («term_∘_» `x "∘" `coeₓ) "=" `x₀) "}")))]
           ":="
           (Term.proj (Term.app `Equivₓ.subtypeEquivCodomain [(Term.hole "_")]) "." `symm))))
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_»
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `x)]
               [":"
                («term{__:_//_}»
                 "{"
                 `x
                 [":" (Term.arrow `σ "→" `K)]
                 "//"
                 («term_=_» («term_∘_» `x "∘" `coeₓ) "=" `x₀)
                 "}")]))
             ", "
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app (Term.paren "(" [`x [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
               "^"
               (Term.app `d [`j]))))
            "="
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `K]))
             ", "
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `σ]))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app
                (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
                [`j])
               "^"
               (Term.app `d [`j])))))
           ":="
           (Term.proj (Term.app `e.sum_comp [(Term.hole "_")]) "." `symm))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `K]))
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Algebra.BigOperators.Basic.«term∏_,_»
               "∏"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
               ", "
               (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
              "*"
              (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i])))))
           ":="
           (Term.app `Fintype.sum_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
             "*"
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `K]))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i])))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_sum)] "]") []) [])]))))
          (calcStep
           («term_=_» (Term.hole "_") "=" (numLit "0"))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
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
                [])]))))])
        [])
       (group (Tactic.intro "intro" [`a]) [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `e'
           [(Term.typeSpec
             ":"
             (Data.Equiv.Basic.«term_≃_»
              (Term.app
               `Sum
               [(«term{__:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")
                («term{__:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")])
              " ≃ "
              `σ))]
           ":="
           (Term.app `Equivₓ.sumCompl [(Term.hole "_")]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `this'
           []
           [(Term.typeSpec ":" (Term.app `Unique [(«term{__:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")]))]
           ":="
           (Term.structInst
            "{"
            []
            [(group
              (Term.structInstField (Term.structInstLVal `default []) ":=" (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩"))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `uniq [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun [(Term.anonymousCtor "⟨" [`j "," `h] "⟩")] "=>" (Term.app `Subtype.val_injective [`h]))))
              [])]
            (Term.optEllipsis [])
            []
            "}"))))
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_»
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `σ]))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app
               (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
               [`j])
              "^"
              (Term.app `d [`j])))
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app
               (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
               [`i])
              "^"
              (Term.app `d [`i]))
             "*"
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders
                [(Lean.binderIdent `j)]
                [":" («term{__:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")]))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app
                (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
                [`j])
               "^"
               (Term.app `d [`j])))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] `e'.prod_comp)
                   ","
                   (Tactic.rwRule [] `Fintype.prod_sum_type)
                   ","
                   (Tactic.rwRule [] `univ_unique)
                   ","
                   (Tactic.rwRule [] `prod_singleton)]
                  "]")
                 [])
                [])
               (group (Tactic.tacticRfl "rfl") [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i]))
             "*"
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders
                [(Lean.binderIdent `j)]
                [":" («term{__:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")]))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app
                (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
                [`j])
               "^"
               (Term.app `d [`j])))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equivₓ.subtype_equiv_codomain_symm_apply_eq)] "]")
                 [])
                [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i]))
             "*"
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))))
           ":="
           (Term.app
            `congr_argₓ
            [(Term.hole "_") (Term.app `Fintype.prod_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
             "*"
             (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i]))))
           ":="
           (Term.app `mul_commₓ [(Term.hole "_") (Term.hole "_")]))])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rintro
              "rintro"
              [(Tactic.rintroPat.one
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hj)]) [])]
                 "⟩"))]
              [])
             [])
            (group
             (Tactic.tacticShow_
              "show"
              («term_=_»
               (Cardinal.SetTheory.Cofinality.«term_^_»
                (Term.app
                 (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
                 [`j])
                "^"
                (Term.app `d [`j]))
               "="
               (Cardinal.SetTheory.Cofinality.«term_^_»
                (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
                "^"
                (Term.app `d [`j]))))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equivₓ.subtype_equiv_codomain_symm_apply_ne)] "]")
              [])
             [])])))
        [])])))
   [])
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl [] [(Term.typeSpec ":" (Term.app `DecidableEq [`K]))] ":=" (Term.app `Classical.decEq [`K]))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
            ", "
            (Term.app `eval [`x `f]))
           "="
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.arrow `σ "→" `K)]))
            ", "
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
             " in "
             `f.support
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.app `f.coeff [`d])
              "*"
              (Algebra.BigOperators.Basic.«term∏_,_»
               "∏"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
               ", "
               (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `eval_eq')] "]"] []) [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
            " in "
            `f.support
            ", "
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.arrow `σ "→" `K)]))
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.app `f.coeff [`d])
              "*"
              (Algebra.BigOperators.Basic.«term∏_,_»
               "∏"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
               ", "
               (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))))
          ":="
          `sum_comm)
         (calcStep («term_=_» (Term.hole "_") "=" (numLit "0")) ":=" (Term.app `sum_eq_zero [(Term.hole "_")]))])
       [])
      (group (Tactic.intro "intro" [`d `hd]) [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hi)]) [])]
            "⟩")])]
        [":"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
          ","
          («term_<_» (Term.app `d [`i]) "<" («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))]
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app `f.exists_degree_lt [(«term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")) `h `hd]))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.arrow `σ "→" `K)]))
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Term.app `f.coeff [`d])
             "*"
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i])))))
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Term.app `f.coeff [`d])
            "*"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.arrow `σ "→" `K)]))
             ", "
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))))
          ":="
          `mul_sum.symm)
         (calcStep
          («term_=_» (Term.hole "_") "=" (numLit "0"))
          ":="
          (Term.app («term_∘_» `mul_eq_zero.mpr "∘" `Or.inr) [(Term.hole "_")]))])
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" (Term.arrow `σ "→" `K)]))
            ", "
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x [`i]) "^" (Term.app `d [`i]))))
           "="
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders
               "("
               [(Lean.binderIdent `x₀)]
               ":"
               (Term.arrow («term{__:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}") "→" `K)
               ")")
              (Lean.bracketedExplicitBinders
               "("
               [(Lean.binderIdent `x)]
               ":"
               («term{__:_//_}»
                "{"
                `x
                [":" (Term.arrow `σ "→" `K)]
                "//"
                («term_=_» («term_∘_» `x "∘" `coeₓ) "=" `x₀)
                "}")
               ")")])
            ", "
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app (Term.paren "(" [`x [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
              "^"
              (Term.app `d [`j])))))
          ":="
          (Term.proj (Term.app `Fintype.sum_fiberwise [(Term.hole "_") (Term.hole "_")]) "." `symm))
         (calcStep
          («term_=_» (Term.hole "_") "=" (numLit "0"))
          ":="
          (Term.app `Fintype.sum_eq_zero [(Term.hole "_") (Term.hole "_")]))])
       [])
      (group (Tactic.intro "intro" [`x₀]) [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `e
          [(Term.typeSpec
            ":"
            (Data.Equiv.Basic.«term_≃_»
             `K
             " ≃ "
             («term{__:_//_}» "{" `x [] "//" («term_=_» («term_∘_» `x "∘" `coeₓ) "=" `x₀) "}")))]
          ":="
          (Term.proj (Term.app `Equivₓ.subtypeEquivCodomain [(Term.hole "_")]) "." `symm))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `x)]
              [":"
               («term{__:_//_}»
                "{"
                `x
                [":" (Term.arrow `σ "→" `K)]
                "//"
                («term_=_» («term_∘_» `x "∘" `coeₓ) "=" `x₀)
                "}")]))
            ", "
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app (Term.paren "(" [`x [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
              "^"
              (Term.app `d [`j]))))
           "="
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `K]))
            ", "
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `σ]))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app
               (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
               [`j])
              "^"
              (Term.app `d [`j])))))
          ":="
          (Term.proj (Term.app `e.sum_comp [(Term.hole "_")]) "." `symm))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `K]))
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
              ", "
              (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
             "*"
             (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i])))))
          ":="
          (Term.app `Fintype.sum_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
            "*"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `K]))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i])))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_sum)] "]") []) [])]))))
         (calcStep
          («term_=_» (Term.hole "_") "=" (numLit "0"))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
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
               [])]))))])
       [])
      (group (Tactic.intro "intro" [`a]) [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `e'
          [(Term.typeSpec
            ":"
            (Data.Equiv.Basic.«term_≃_»
             (Term.app
              `Sum
              [(«term{__:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")
               («term{__:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")])
             " ≃ "
             `σ))]
          ":="
          (Term.app `Equivₓ.sumCompl [(Term.hole "_")]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `this'
          []
          [(Term.typeSpec ":" (Term.app `Unique [(«term{__:_//_}» "{" `j [] "//" («term_=_» `j "=" `i) "}")]))]
          ":="
          (Term.structInst
           "{"
           []
           [(group
             (Term.structInstField (Term.structInstLVal `default []) ":=" (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩"))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `uniq [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun [(Term.anonymousCtor "⟨" [`j "," `h] "⟩")] "=>" (Term.app `Subtype.val_injective [`h]))))
             [])]
           (Term.optEllipsis [])
           []
           "}"))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Algebra.BigOperators.Basic.«term∏_,_»
            "∏"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `σ]))
            ", "
            (Cardinal.SetTheory.Cofinality.«term_^_»
             (Term.app
              (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
              [`j])
             "^"
             (Term.app `d [`j])))
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Cardinal.SetTheory.Cofinality.«term_^_»
             (Term.app
              (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
              [`i])
             "^"
             (Term.app `d [`i]))
            "*"
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `j)]
               [":" («term{__:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")]))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app
               (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
               [`j])
              "^"
              (Term.app `d [`j])))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `e'.prod_comp)
                  ","
                  (Tactic.rwRule [] `Fintype.prod_sum_type)
                  ","
                  (Tactic.rwRule [] `univ_unique)
                  ","
                  (Tactic.rwRule [] `prod_singleton)]
                 "]")
                [])
               [])
              (group (Tactic.tacticRfl "rfl") [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i]))
            "*"
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `j)]
               [":" («term{__:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")]))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app
               (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
               [`j])
              "^"
              (Term.app `d [`j])))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equivₓ.subtype_equiv_codomain_symm_apply_eq)] "]")
                [])
               [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i]))
            "*"
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))))
          ":="
          (Term.app
           `congr_argₓ
           [(Term.hole "_") (Term.app `Fintype.prod_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
            "*"
            (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i]))))
          ":="
          (Term.app `mul_commₓ [(Term.hole "_") (Term.hole "_")]))])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rintro
             "rintro"
             [(Tactic.rintroPat.one
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hj)]) [])]
                "⟩"))]
             [])
            [])
           (group
            (Tactic.tacticShow_
             "show"
             («term_=_»
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app
                (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
                [`j])
               "^"
               (Term.app `d [`j]))
              "="
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
               "^"
               (Term.app `d [`j]))))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equivₓ.subtype_equiv_codomain_symm_apply_ne)] "]")
             [])
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hj)]) [])]
           "⟩"))]
        [])
       [])
      (group
       (Tactic.tacticShow_
        "show"
        («term_=_»
         (Cardinal.SetTheory.Cofinality.«term_^_»
          (Term.app (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
          "^"
          (Term.app `d [`j]))
         "="
         (Cardinal.SetTheory.Cofinality.«term_^_»
          (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
          "^"
          (Term.app `d [`j]))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equivₓ.subtype_equiv_codomain_symm_apply_ne)] "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equivₓ.subtype_equiv_codomain_symm_apply_ne)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Equivₓ.subtype_equiv_codomain_symm_apply_ne
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticShow_
   "show"
   («term_=_»
    (Cardinal.SetTheory.Cofinality.«term_^_»
     (Term.app (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
     "^"
     (Term.app `d [`j]))
    "="
    (Cardinal.SetTheory.Cofinality.«term_^_»
     (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
     "^"
     (Term.app `d [`j]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticShow_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.app (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
    "^"
    (Term.app `d [`j]))
   "="
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
    "^"
    (Term.app `d [`j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
   "^"
   (Term.app `d [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [`j])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`j "," `hj] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hj
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `x₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `x₀ [(Term.anonymousCtor "⟨" [`j "," `hj] "⟩")])
   "^"
   (Term.app `d [`j]))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
   "^"
   (Term.app `d [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [`j])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow `σ "→" `K)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  `σ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `e [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
   "^"
   (Term.app `d [`j]))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one
     (Tactic.rcasesPat.tuple
      "⟨"
      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hj)]) [])]
      "⟩"))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_=_»
      (Algebra.BigOperators.Basic.«term∏_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `σ]))
       ", "
       (Cardinal.SetTheory.Cofinality.«term_^_»
        (Term.app (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
        "^"
        (Term.app `d [`j])))
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Cardinal.SetTheory.Cofinality.«term_^_»
        (Term.app (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`i])
        "^"
        (Term.app `d [`i]))
       "*"
       (Algebra.BigOperators.Basic.«term∏_,_»
        "∏"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `j)]
          [":" («term{__:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")]))
        ", "
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Term.app (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
         "^"
         (Term.app `d [`j])))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `e'.prod_comp)
             ","
             (Tactic.rwRule [] `Fintype.prod_sum_type)
             ","
             (Tactic.rwRule [] `univ_unique)
             ","
             (Tactic.rwRule [] `prod_singleton)]
            "]")
           [])
          [])
         (group (Tactic.tacticRfl "rfl") [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i]))
       "*"
       (Algebra.BigOperators.Basic.«term∏_,_»
        "∏"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `j)]
          [":" («term{__:_//_}» "{" `j [] "//" («term_≠_» `j "≠" `i) "}")]))
        ", "
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Term.app (Term.paren "(" [(Term.app `e [`a]) [(Term.typeAscription ":" (Term.arrow `σ "→" `K))]] ")") [`j])
         "^"
         (Term.app `d [`j])))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equivₓ.subtype_equiv_codomain_symm_apply_eq)] "]")
           [])
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i]))
       "*"
       (Algebra.BigOperators.Basic.«term∏_,_»
        "∏"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
        ", "
        (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))))
     ":="
     (Term.app
      `congr_argₓ
      [(Term.hole "_") (Term.app `Fintype.prod_congr [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Algebra.BigOperators.Basic.«term∏_,_»
        "∏"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
        ", "
        (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
       "*"
       (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i]))))
     ":="
     (Term.app `mul_commₓ [(Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_commₓ [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_commₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Algebra.BigOperators.Basic.«term∏_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
     ", "
     (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
    "*"
    (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Algebra.BigOperators.Basic.«term∏_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
    ", "
    (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
   "*"
   (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `a "^" (Term.app `d [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Algebra.BigOperators.Basic.«term∏_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
   ", "
   (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» (Term.app `x₀ [`j]) "^" (Term.app `d [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [`j])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `x₀ [`j])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `x₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
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
theorem
  MvPolynomial.sum_mv_polynomial_eq_zero
  [ DecidableEq σ ] ( f : MvPolynomial σ K ) ( h : f.total_degree < q - 1 * Fintype.card σ ) : ∑ x , eval x f = 0
  :=
    by
      have : DecidableEq K := Classical.decEq K
        calc
          ∑ x , eval x f = ∑ x : σ → K , ∑ d in f.support , f.coeff d * ∏ i , x i ^ d i := by simp only [ eval_eq' ]
            _ = ∑ d in f.support , ∑ x : σ → K , f.coeff d * ∏ i , x i ^ d i := sum_comm
            _ = 0 := sum_eq_zero _
        intro d hd
        obtain ⟨ i , hi ⟩ : ∃ i , d i < q - 1
        exact f.exists_degree_lt q - 1 h hd
        calc
          ∑ x : σ → K , f.coeff d * ∏ i , x i ^ d i = f.coeff d * ∑ x : σ → K , ∏ i , x i ^ d i := mul_sum.symm
            _ = 0 := mul_eq_zero.mpr ∘ Or.inr _
        calc
          ∑ x : σ → K , ∏ i , x i ^ d i
                =
                ∑ ( x₀ : { j // j ≠ i } → K ) ( x : { x : σ → K // x ∘ coeₓ = x₀ } ) , ∏ j , ( x : σ → K ) j ^ d j
              :=
              Fintype.sum_fiberwise _ _ . symm
            _ = 0 := Fintype.sum_eq_zero _ _
        intro x₀
        let e : K ≃ { x // x ∘ coeₓ = x₀ } := Equivₓ.subtypeEquivCodomain _ . symm
        calc
          ∑ x : { x : σ → K // x ∘ coeₓ = x₀ } , ∏ j , ( x : σ → K ) j ^ d j
                =
                ∑ a : K , ∏ j : σ , ( e a : σ → K ) j ^ d j
              :=
              e.sum_comp _ . symm
            _ = ∑ a : K , ∏ j , x₀ j ^ d j * a ^ d i := Fintype.sum_congr _ _ _
            _ = ∏ j , x₀ j ^ d j * ∑ a : K , a ^ d i := by rw [ mul_sum ]
            _ = 0 := by rw [ sum_pow_lt_card_sub_one _ hi , mul_zero ]
        intro a
        let e' : Sum { j // j = i } { j // j ≠ i } ≃ σ := Equivₓ.sumCompl _
        let
          this' : Unique { j // j = i } := { default := ⟨ i , rfl ⟩ , uniq := fun ⟨ j , h ⟩ => Subtype.val_injective h }
        calc
          ∏ j : σ , ( e a : σ → K ) j ^ d j = ( e a : σ → K ) i ^ d i * ∏ j : { j // j ≠ i } , ( e a : σ → K ) j ^ d j
              :=
              by rw [ ← e'.prod_comp , Fintype.prod_sum_type , univ_unique , prod_singleton ] rfl
            _ = a ^ d i * ∏ j : { j // j ≠ i } , ( e a : σ → K ) j ^ d j
              :=
              by rw [ Equivₓ.subtype_equiv_codomain_symm_apply_eq ]
            _ = a ^ d i * ∏ j , x₀ j ^ d j := congr_argₓ _ Fintype.prod_congr _ _ _
            _ = ∏ j , x₀ j ^ d j * a ^ d i := mul_commₓ _ _
        ·
          rintro ⟨ j , hj ⟩
            show ( e a : σ → K ) j ^ d j = x₀ ⟨ j , hj ⟩ ^ d j
            rw [ Equivₓ.subtype_equiv_codomain_symm_apply_ne ]

variable [DecidableEq K] [DecidableEq σ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The Chevalley–Warning theorem.\nLet `(f i)` be a finite family of multivariate polynomials\nin finitely many variables (`X s`, `s : σ`) over a finite field of characteristic `p`.\nAssume that the sum of the total degrees of the `f i` is less than the cardinality of `σ`.\nThen the number of common solutions of the `f i` is divisible by `p`. -/")]
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
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `ι "→" (Term.app `MvPolynomial [`σ `K]))] "}")
    (Term.explicitBinder
     "("
     [`h]
     [":"
      («term_<_»
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
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
    (Init.Core.«term_∣_»
     `p
     " ∣ "
     (Term.app
      `Fintype.card
      [(«term{__:_//_}»
        "{"
        `x
        [":" (Term.arrow `σ "→" `K)]
        "//"
        (Term.forall
         "∀"
         []
         ","
         (Mathlib.ExtendedBinder.«term∀___,_»
          "∀"
          `i
          («binderTerm∈_» "∈" `s)
          ","
          (Term.forall "∀" [] "," («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (numLit "0")))))
        "}")]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hq []]
           [(Term.typeSpec
             ":"
             («term_<_» (numLit "0") "<" («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] `Fintype.card_units) "," (Tactic.rwRule [] `Fintype.card_pos_iff)]
                  "]")
                 [])
                [])
               (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(numLit "1")] "⟩")) [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `S
           [(Term.typeSpec ":" (Term.app `Finset [(Term.arrow `σ "→" `K)]))]
           ":="
           (Set.«term{_|_}_1»
            "{"
            («term_∈_» `x "∈" `univ)
            "|"
            (Term.forall
             "∀"
             []
             ","
             (Mathlib.ExtendedBinder.«term∀___,_»
              "∀"
              `i
              («binderTerm∈_» "∈" `s)
              ","
              (Term.forall "∀" [] "," («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (numLit "0")))))
            "}"))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hS []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`x] [(Term.typeSpec ":" (Term.arrow `σ "→" `K))])]
              ","
              («term_↔_»
               (Init.Core.«term_∈_» `x " ∈ " `S)
               "↔"
               (Term.forall
                "∀"
                [(Term.simpleBinder [`i] [(Term.typeSpec ":" `ι)])]
                ","
                (Term.arrow
                 (Init.Core.«term_∈_» `i " ∈ " `s)
                 "→"
                 («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (numLit "0")))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`x]) [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `S)
                   ","
                   (Tactic.simpLemma [] [] `true_andₓ)
                   ","
                   (Tactic.simpLemma [] [] `sep_def)
                   ","
                   (Tactic.simpLemma [] [] `mem_filter)
                   ","
                   (Tactic.simpLemma [] [] `mem_univ)]
                  "]"]
                 [])
                [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `F
           [(Term.typeSpec ":" (Term.app `MvPolynomial [`σ `K]))]
           ":="
           (Algebra.BigOperators.Basic.«term∏_in_,_»
            "∏"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            " in "
            `s
            ", "
            («term_-_»
             (numLit "1")
             "-"
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app `f [`i])
              "^"
              («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hF []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`x] [])]
              ","
              («term_=_»
               (Term.app `eval [`x `F])
               "="
               (termIfThenElse "if" (Init.Core.«term_∈_» `x " ∈ " `S) "then" (numLit "1") "else" (numLit "0")))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`x]) [])
               (group
                (tacticCalc_
                 "calc"
                 [(calcStep
                   («term_=_»
                    (Term.app `eval [`x `F])
                    "="
                    (Algebra.BigOperators.Basic.«term∏_in_,_»
                     "∏"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                     " in "
                     `s
                     ", "
                     (Term.app
                      `eval
                      [`x
                       («term_-_»
                        (numLit "1")
                        "-"
                        (Cardinal.SetTheory.Cofinality.«term_^_»
                         (Term.app `f [`i])
                         "^"
                         («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))])))
                   ":="
                   (Term.app `eval_prod [`s (Term.hole "_") `x]))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (termIfThenElse "if" (Init.Core.«term_∈_» `x " ∈ " `S) "then" (numLit "1") "else" (numLit "0")))
                   ":="
                   (Term.hole "_"))])
                [])
               (group
                (Tactic.simp
                 "simp"
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
                [])
               (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `hx) (Lean.binderIdent `hx)]]) [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.apply "apply" `Finset.prod_eq_one) [])
                    (group (Tactic.intro "intro" [`i `hi]) [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hS)] "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                     [])
                    (group
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
                      [])
                     [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.obtain
                      "obtain"
                      [(Tactic.rcasesPatMed
                        [(Tactic.rcasesPat.tuple
                          "⟨"
                          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])
                           ","
                           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hi)]) [])
                           ","
                           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                          "⟩")])]
                      [":"
                       («term∃_,_»
                        "∃"
                        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
                        ","
                        («term_∧_»
                         (Init.Core.«term_∈_» `i " ∈ " `s)
                         "∧"
                         («term_≠_» (Term.app `eval [`x (Term.app `f [`i])]) "≠" (numLit "0"))))]
                      [])
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.simpa
                           "simpa"
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `hS)
                             ","
                             (Tactic.simpLemma [] [] `not_forall)
                             ","
                             (Tactic.simpLemma [] [] `not_imp)]
                            "]"]
                           []
                           ["using" `hx])
                          [])])))
                     [])
                    (group (Tactic.apply "apply" (Term.app `Finset.prod_eq_zero [`hi])) [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         []
                         (Term.app `pow_card_sub_one_eq_one [(Term.app `eval [`x (Term.app `f [`i])]) `hx]))
                        ","
                        (Tactic.rwRule [] `sub_self)]
                       "]")
                      [])
                     [])])))
                [])]))))))
        [])
       (group
        (Tactic.have''
         "have"
         [`key []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             ", "
             (Term.app `eval [`x `F]))
            "="
            (Term.app
             `Fintype.card
             [(«term{__:_//_}»
               "{"
               `x
               [":" (Term.arrow `σ "→" `K)]
               "//"
               (Term.forall
                "∀"
                []
                ","
                (Mathlib.ExtendedBinder.«term∀___,_»
                 "∀"
                 `i
                 («binderTerm∈_» "∈" `s)
                 ","
                 (Term.forall "∀" [] "," («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (numLit "0")))))
               "}")])))])
        [])
       (group
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
           (Tactic.rwRule ["←"] (Term.app `Fintype.sum_extend_by_zero [`S]))
           ","
           (Tactic.rwRule
            []
            (Term.app
             `sum_congr
             [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `hF [`x])))]))]
          "]")
         [])
        [])
       (group
        (Tactic.tacticShow_
         "show"
         (Init.Core.«term_∣_»
          `p
          " ∣ "
          (Term.app
           `Fintype.card
           [(«term{__:_//_}»
             "{"
             `x
             []
             "//"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`i] [(Term.typeSpec ":" `ι)])]
              ","
              (Term.arrow
               (Init.Core.«term_∈_» `i " ∈ " `s)
               "→"
               («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (numLit "0"))))
             "}")])))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule ["←"] (Term.app `CharP.cast_eq_zero_iff [`K])) "," (Tactic.rwRule ["←"] `key)]
          "]")
         [])
        [])
       (group
        (Tactic.tacticShow_
         "show"
         («term_=_»
          (Algebra.BigOperators.Basic.«term∑_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           ", "
           (Term.app `eval [`x `F]))
          "="
          (numLit "0")))
        [])
       (group (Tactic.apply "apply" `F.sum_mv_polynomial_eq_zero) [])
       (group
        (Tactic.tacticShow_
         "show"
         («term_<_»
          `F.total_degree
          "<"
          (Finset.Data.Finset.Fold.«term_*_»
           («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
           "*"
           (Term.app `Fintype.card [`σ]))))
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_≤_»
            `F.total_degree
            "≤"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             " in "
             `s
             ", "
             (Term.proj
              («term_-_»
               (numLit "1")
               "-"
               (Cardinal.SetTheory.Cofinality.«term_^_»
                (Term.app `f [`i])
                "^"
                («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
              "."
              `totalDegree)))
           ":="
           (Term.app `total_degree_finset_prod [`s (Term.hole "_")]))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             " in "
             `s
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
              "*"
              (Term.proj (Term.app `f [`i]) "." `totalDegree))))
           ":="
           («term_$__»
            `sum_le_sum
            "$"
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
             "*"
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
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
            (Finset.Data.Finset.Fold.«term_*_»
             («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
             "*"
             (Term.app `Fintype.card [`σ])))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mul_lt_mul_left [`hq]))] "]") [])
                [])]))))])
        [])
       (group
        (Tactic.tacticShow_
         "show"
         («term_≤_»
          (Term.proj
           («term_-_»
            (numLit "1")
            "-"
            (Cardinal.SetTheory.Cofinality.«term_^_»
             (Term.app `f [`i])
             "^"
             («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
           "."
           `totalDegree)
          "≤"
          (Finset.Data.Finset.Fold.«term_*_»
           («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
           "*"
           (Term.proj (Term.app `f [`i]) "." `totalDegree))))
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_≤_»
            (Term.proj
             («term_-_»
              (numLit "1")
              "-"
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app `f [`i])
               "^"
               («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
             "."
             `totalDegree)
            "≤"
            (Term.app
             `max
             [(Term.proj
               (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (Term.app `MvPolynomial [`σ `K]))]] ")")
               "."
               `totalDegree)
              (Term.proj
               (Cardinal.SetTheory.Cofinality.«term_^_»
                (Term.app `f [`i])
                "^"
                («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
               "."
               `totalDegree)]))
           ":="
           (Term.app `total_degree_sub [(Term.hole "_") (Term.hole "_")]))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Term.proj
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app `f [`i])
              "^"
              («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
             "."
             `totalDegree))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `max_eq_rightₓ)
                   ","
                   (Tactic.simpLemma [] [] `Nat.zero_leₓ)
                   ","
                   (Tactic.simpLemma [] [] `total_degree_one)]
                  "]"]
                 [])
                [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
             "*"
             (Term.proj (Term.app `f [`i]) "." `totalDegree)))
           ":="
           (Term.app `total_degree_pow [(Term.hole "_") (Term.hole "_")]))])
        [])])))
   [])
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hq []]
          [(Term.typeSpec
            ":"
            («term_<_» (numLit "0") "<" («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `Fintype.card_units) "," (Tactic.rwRule [] `Fintype.card_pos_iff)]
                 "]")
                [])
               [])
              (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(numLit "1")] "⟩")) [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `S
          [(Term.typeSpec ":" (Term.app `Finset [(Term.arrow `σ "→" `K)]))]
          ":="
          (Set.«term{_|_}_1»
           "{"
           («term_∈_» `x "∈" `univ)
           "|"
           (Term.forall
            "∀"
            []
            ","
            (Mathlib.ExtendedBinder.«term∀___,_»
             "∀"
             `i
             («binderTerm∈_» "∈" `s)
             ","
             (Term.forall "∀" [] "," («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (numLit "0")))))
           "}"))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hS []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`x] [(Term.typeSpec ":" (Term.arrow `σ "→" `K))])]
             ","
             («term_↔_»
              (Init.Core.«term_∈_» `x " ∈ " `S)
              "↔"
              (Term.forall
               "∀"
               [(Term.simpleBinder [`i] [(Term.typeSpec ":" `ι)])]
               ","
               (Term.arrow
                (Init.Core.«term_∈_» `i " ∈ " `s)
                "→"
                («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (numLit "0")))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`x]) [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `S)
                  ","
                  (Tactic.simpLemma [] [] `true_andₓ)
                  ","
                  (Tactic.simpLemma [] [] `sep_def)
                  ","
                  (Tactic.simpLemma [] [] `mem_filter)
                  ","
                  (Tactic.simpLemma [] [] `mem_univ)]
                 "]"]
                [])
               [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `F
          [(Term.typeSpec ":" (Term.app `MvPolynomial [`σ `K]))]
          ":="
          (Algebra.BigOperators.Basic.«term∏_in_,_»
           "∏"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
           " in "
           `s
           ", "
           («term_-_»
            (numLit "1")
            "-"
            (Cardinal.SetTheory.Cofinality.«term_^_»
             (Term.app `f [`i])
             "^"
             («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hF []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`x] [])]
             ","
             («term_=_»
              (Term.app `eval [`x `F])
              "="
              (termIfThenElse "if" (Init.Core.«term_∈_» `x " ∈ " `S) "then" (numLit "1") "else" (numLit "0")))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`x]) [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_=_»
                   (Term.app `eval [`x `F])
                   "="
                   (Algebra.BigOperators.Basic.«term∏_in_,_»
                    "∏"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                    " in "
                    `s
                    ", "
                    (Term.app
                     `eval
                     [`x
                      («term_-_»
                       (numLit "1")
                       "-"
                       (Cardinal.SetTheory.Cofinality.«term_^_»
                        (Term.app `f [`i])
                        "^"
                        («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))])))
                  ":="
                  (Term.app `eval_prod [`s (Term.hole "_") `x]))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (termIfThenElse "if" (Init.Core.«term_∈_» `x " ∈ " `S) "then" (numLit "1") "else" (numLit "0")))
                  ":="
                  (Term.hole "_"))])
               [])
              (group
               (Tactic.simp
                "simp"
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
               [])
              (group (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `hx) (Lean.binderIdent `hx)]]) [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.apply "apply" `Finset.prod_eq_one) [])
                   (group (Tactic.intro "intro" [`i `hi]) [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hS)] "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                    [])
                   (group
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
                     [])
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.obtain
                     "obtain"
                     [(Tactic.rcasesPatMed
                       [(Tactic.rcasesPat.tuple
                         "⟨"
                         [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hi)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                         "⟩")])]
                     [":"
                      («term∃_,_»
                       "∃"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
                       ","
                       («term_∧_»
                        (Init.Core.«term_∈_» `i " ∈ " `s)
                        "∧"
                        («term_≠_» (Term.app `eval [`x (Term.app `f [`i])]) "≠" (numLit "0"))))]
                     [])
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.simpa
                          "simpa"
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `hS)
                            ","
                            (Tactic.simpLemma [] [] `not_forall)
                            ","
                            (Tactic.simpLemma [] [] `not_imp)]
                           "]"]
                          []
                          ["using" `hx])
                         [])])))
                    [])
                   (group (Tactic.apply "apply" (Term.app `Finset.prod_eq_zero [`hi])) [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        []
                        (Term.app `pow_card_sub_one_eq_one [(Term.app `eval [`x (Term.app `f [`i])]) `hx]))
                       ","
                       (Tactic.rwRule [] `sub_self)]
                      "]")
                     [])
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.have''
        "have"
        [`key []]
        [(Term.typeSpec
          ":"
          («term_=_»
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
            ", "
            (Term.app `eval [`x `F]))
           "="
           (Term.app
            `Fintype.card
            [(«term{__:_//_}»
              "{"
              `x
              [":" (Term.arrow `σ "→" `K)]
              "//"
              (Term.forall
               "∀"
               []
               ","
               (Mathlib.ExtendedBinder.«term∀___,_»
                "∀"
                `i
                («binderTerm∈_» "∈" `s)
                ","
                (Term.forall "∀" [] "," («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (numLit "0")))))
              "}")])))])
       [])
      (group
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
          (Tactic.rwRule ["←"] (Term.app `Fintype.sum_extend_by_zero [`S]))
          ","
          (Tactic.rwRule
           []
           (Term.app
            `sum_congr
            [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `hF [`x])))]))]
         "]")
        [])
       [])
      (group
       (Tactic.tacticShow_
        "show"
        (Init.Core.«term_∣_»
         `p
         " ∣ "
         (Term.app
          `Fintype.card
          [(«term{__:_//_}»
            "{"
            `x
            []
            "//"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`i] [(Term.typeSpec ":" `ι)])]
             ","
             (Term.arrow
              (Init.Core.«term_∈_» `i " ∈ " `s)
              "→"
              («term_=_» (Term.app `eval [`x (Term.app `f [`i])]) "=" (numLit "0"))))
            "}")])))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] (Term.app `CharP.cast_eq_zero_iff [`K])) "," (Tactic.rwRule ["←"] `key)]
         "]")
        [])
       [])
      (group
       (Tactic.tacticShow_
        "show"
        («term_=_»
         (Algebra.BigOperators.Basic.«term∑_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          ", "
          (Term.app `eval [`x `F]))
         "="
         (numLit "0")))
       [])
      (group (Tactic.apply "apply" `F.sum_mv_polynomial_eq_zero) [])
      (group
       (Tactic.tacticShow_
        "show"
        («term_<_»
         `F.total_degree
         "<"
         (Finset.Data.Finset.Fold.«term_*_»
          («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
          "*"
          (Term.app `Fintype.card [`σ]))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           `F.total_degree
           "≤"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            " in "
            `s
            ", "
            (Term.proj
             («term_-_»
              (numLit "1")
              "-"
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app `f [`i])
               "^"
               («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
             "."
             `totalDegree)))
          ":="
          (Term.app `total_degree_finset_prod [`s (Term.hole "_")]))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            " in "
            `s
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
             "*"
             (Term.proj (Term.app `f [`i]) "." `totalDegree))))
          ":="
          («term_$__»
           `sum_le_sum
           "$"
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
            "*"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
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
           (Finset.Data.Finset.Fold.«term_*_»
            («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
            "*"
            (Term.app `Fintype.card [`σ])))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mul_lt_mul_left [`hq]))] "]") [])
               [])]))))])
       [])
      (group
       (Tactic.tacticShow_
        "show"
        («term_≤_»
         (Term.proj
          («term_-_»
           (numLit "1")
           "-"
           (Cardinal.SetTheory.Cofinality.«term_^_»
            (Term.app `f [`i])
            "^"
            («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
          "."
          `totalDegree)
         "≤"
         (Finset.Data.Finset.Fold.«term_*_»
          («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
          "*"
          (Term.proj (Term.app `f [`i]) "." `totalDegree))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           (Term.proj
            («term_-_»
             (numLit "1")
             "-"
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app `f [`i])
              "^"
              («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
            "."
            `totalDegree)
           "≤"
           (Term.app
            `max
            [(Term.proj
              (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (Term.app `MvPolynomial [`σ `K]))]] ")")
              "."
              `totalDegree)
             (Term.proj
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.app `f [`i])
               "^"
               («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
              "."
              `totalDegree)]))
          ":="
          (Term.app `total_degree_sub [(Term.hole "_") (Term.hole "_")]))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Term.proj
            (Cardinal.SetTheory.Cofinality.«term_^_»
             (Term.app `f [`i])
             "^"
             («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
            "."
            `totalDegree))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `max_eq_rightₓ)
                  ","
                  (Tactic.simpLemma [] [] `Nat.zero_leₓ)
                  ","
                  (Tactic.simpLemma [] [] `total_degree_one)]
                 "]"]
                [])
               [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
            "*"
            (Term.proj (Term.app `f [`i]) "." `totalDegree)))
          ":="
          (Term.app `total_degree_pow [(Term.hole "_") (Term.hole "_")]))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_≤_»
      (Term.proj
       («term_-_»
        (numLit "1")
        "-"
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Term.app `f [`i])
         "^"
         («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
       "."
       `totalDegree)
      "≤"
      (Term.app
       `max
       [(Term.proj
         (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (Term.app `MvPolynomial [`σ `K]))]] ")")
         "."
         `totalDegree)
        (Term.proj
         (Cardinal.SetTheory.Cofinality.«term_^_»
          (Term.app `f [`i])
          "^"
          («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
         "."
         `totalDegree)]))
     ":="
     (Term.app `total_degree_sub [(Term.hole "_") (Term.hole "_")]))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Term.proj
       (Cardinal.SetTheory.Cofinality.«term_^_»
        (Term.app `f [`i])
        "^"
        («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
       "."
       `totalDegree))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `max_eq_rightₓ)
             ","
             (Tactic.simpLemma [] [] `Nat.zero_leₓ)
             ","
             (Tactic.simpLemma [] [] `total_degree_one)]
            "]"]
           [])
          [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
       "*"
       (Term.proj (Term.app `f [`i]) "." `totalDegree)))
     ":="
     (Term.app `total_degree_pow [(Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `total_degree_pow [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `total_degree_pow
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_»
    («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
    "*"
    (Term.proj (Term.app `f [`i]) "." `totalDegree)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
   "*"
   (Term.proj (Term.app `f [`i]) "." `totalDegree))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `f [`i]) "." `totalDegree)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`i]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (FieldTheory.ChevalleyWarning.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.ChevalleyWarning.termq', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `max_eq_rightₓ)
          ","
          (Tactic.simpLemma [] [] `Nat.zero_leₓ)
          ","
          (Tactic.simpLemma [] [] `total_degree_one)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `max_eq_rightₓ)
     ","
     (Tactic.simpLemma [] [] `Nat.zero_leₓ)
     ","
     (Tactic.simpLemma [] [] `total_degree_one)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `total_degree_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nat.zero_leₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `max_eq_rightₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Term.proj
    (Cardinal.SetTheory.Cofinality.«term_^_»
     (Term.app `f [`i])
     "^"
     («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
    "."
    `totalDegree))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.app `f [`i])
    "^"
    («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
   "."
   `totalDegree)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `f [`i])
   "^"
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (FieldTheory.ChevalleyWarning.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.ChevalleyWarning.termq', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `f [`i])
   "^"
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `total_degree_sub [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `total_degree_sub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.proj
    («term_-_»
     (numLit "1")
     "-"
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.app `f [`i])
      "^"
      («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
    "."
    `totalDegree)
   "≤"
   (Term.app
    `max
    [(Term.proj
      (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (Term.app `MvPolynomial [`σ `K]))]] ")")
      "."
      `totalDegree)
     (Term.proj
      (Cardinal.SetTheory.Cofinality.«term_^_»
       (Term.app `f [`i])
       "^"
       («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
      "."
      `totalDegree)]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `max
   [(Term.proj
     (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (Term.app `MvPolynomial [`σ `K]))]] ")")
     "."
     `totalDegree)
    (Term.proj
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.app `f [`i])
      "^"
      («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
     "."
     `totalDegree)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.app `f [`i])
    "^"
    («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
   "."
   `totalDegree)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `f [`i])
   "^"
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (FieldTheory.ChevalleyWarning.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.ChevalleyWarning.termq', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `f [`i])
   "^"
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj
   (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (Term.app `MvPolynomial [`σ `K]))]] ")")
   "."
   `totalDegree)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (Term.app `MvPolynomial [`σ `K]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `MvPolynomial [`σ `K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `σ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `MvPolynomial
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `max
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.proj
   («term_-_»
    (numLit "1")
    "-"
    (Cardinal.SetTheory.Cofinality.«term_^_»
     (Term.app `f [`i])
     "^"
     («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
   "."
   `totalDegree)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_-_»
   (numLit "1")
   "-"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.app `f [`i])
    "^"
    («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `f [`i])
   "^"
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (FieldTheory.ChevalleyWarning.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.ChevalleyWarning.termq', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `f [`i])
   "^"
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_-_»
   (numLit "1")
   "-"
   (Term.paren
    "("
    [(Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.app `f [`i])
      "^"
      («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
     []]
    ")"))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticShow_
   "show"
   («term_≤_»
    (Term.proj
     («term_-_»
      (numLit "1")
      "-"
      (Cardinal.SetTheory.Cofinality.«term_^_»
       (Term.app `f [`i])
       "^"
       («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
     "."
     `totalDegree)
    "≤"
    (Finset.Data.Finset.Fold.«term_*_»
     («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
     "*"
     (Term.proj (Term.app `f [`i]) "." `totalDegree))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticShow_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.proj
    («term_-_»
     (numLit "1")
     "-"
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.app `f [`i])
      "^"
      («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
    "."
    `totalDegree)
   "≤"
   (Finset.Data.Finset.Fold.«term_*_»
    («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
    "*"
    (Term.proj (Term.app `f [`i]) "." `totalDegree)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
   "*"
   (Term.proj (Term.app `f [`i]) "." `totalDegree))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `f [`i]) "." `totalDegree)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`i]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (FieldTheory.ChevalleyWarning.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.ChevalleyWarning.termq', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.proj
   («term_-_»
    (numLit "1")
    "-"
    (Cardinal.SetTheory.Cofinality.«term_^_»
     (Term.app `f [`i])
     "^"
     («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
   "."
   `totalDegree)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_-_»
   (numLit "1")
   "-"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.app `f [`i])
    "^"
    («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `f [`i])
   "^"
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (FieldTheory.ChevalleyWarning.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.ChevalleyWarning.termq', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `f [`i])
   "^"
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_-_»
   (numLit "1")
   "-"
   (Term.paren
    "("
    [(Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.app `f [`i])
      "^"
      («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")))
     []]
    ")"))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_≤_»
      `F.total_degree
      "≤"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       `s
       ", "
       (Term.proj
        («term_-_»
         (numLit "1")
         "-"
         (Cardinal.SetTheory.Cofinality.«term_^_»
          (Term.app `f [`i])
          "^"
          («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))))
        "."
        `totalDegree)))
     ":="
     (Term.app `total_degree_finset_prod [`s (Term.hole "_")]))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       `s
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
        "*"
        (Term.proj (Term.app `f [`i]) "." `totalDegree))))
     ":="
     («term_$__»
      `sum_le_sum
      "$"
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
       "*"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
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
      (Finset.Data.Finset.Fold.«term_*_»
       («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
       "*"
       (Term.app `Fintype.card [`σ])))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mul_lt_mul_left [`hq]))] "]") [])
          [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mul_lt_mul_left [`hq]))] "]") [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mul_lt_mul_left [`hq]))] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticRwa__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_lt_mul_left [`hq])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_lt_mul_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_»
   (Term.hole "_")
   "<"
   (Finset.Data.Finset.Fold.«term_*_»
    («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
    "*"
    (Term.app `Fintype.card [`σ])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
   "*"
   (Term.app `Fintype.card [`σ]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Fintype.card [`σ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `σ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fintype.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (FieldTheory.ChevalleyWarning.termq "q")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.ChevalleyWarning.termq', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1")) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  `mul_sum.symm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
    "*"
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s
     ", "
     (Term.proj (Term.app `f [`i]) "." `totalDegree))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   («term_-_» (FieldTheory.ChevalleyWarning.termq "q") "-" (numLit "1"))
   "*"
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s
    ", "
    (Term.proj (Term.app `f [`i]) "." `totalDegree)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.proj (Term.app `f [`i]) "." `totalDegree))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `f [`i]) "." `totalDegree)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`i]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
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
      : p ∣ Fintype.card { x : σ → K // ∀ , ∀ i ∈ s , ∀ , eval x f i = 0 }
    :=
      by
        have hq : 0 < q - 1 := by rw [ ← Fintype.card_units , Fintype.card_pos_iff ] exact ⟨ 1 ⟩
          let S : Finset σ → K := { x ∈ univ | ∀ , ∀ i ∈ s , ∀ , eval x f i = 0 }
          have
            hS
              : ∀ x : σ → K , x ∈ S ↔ ∀ i : ι , i ∈ s → eval x f i = 0
              :=
              by intro x simp only [ S , true_andₓ , sep_def , mem_filter , mem_univ ]
          let F : MvPolynomial σ K := ∏ i in s , 1 - f i ^ q - 1
          have
            hF
              : ∀ x , eval x F = if x ∈ S then 1 else 0
              :=
              by
                intro x
                  calc eval x F = ∏ i in s , eval x 1 - f i ^ q - 1 := eval_prod s _ x _ = if x ∈ S then 1 else 0 := _
                  simp only [ eval x . map_sub , eval x . map_pow , eval x . map_one ]
                  split_ifs with hx hx
                  · apply Finset.prod_eq_one intro i hi rw [ hS ] at hx rw [ hx i hi , zero_pow hq , sub_zero ]
                  ·
                    obtain ⟨ i , hi , hx ⟩ : ∃ i : ι , i ∈ s ∧ eval x f i ≠ 0
                      · simpa only [ hS , not_forall , not_imp ] using hx
                      apply Finset.prod_eq_zero hi
                      rw [ pow_card_sub_one_eq_one eval x f i hx , sub_self ]
          have key : ∑ x , eval x F = Fintype.card { x : σ → K // ∀ , ∀ i ∈ s , ∀ , eval x f i = 0 }
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
            F.total_degree ≤ ∑ i in s , 1 - f i ^ q - 1 . totalDegree := total_degree_finset_prod s _
              _ ≤ ∑ i in s , q - 1 * f i . totalDegree := sum_le_sum $ fun i hi => _
              _ = q - 1 * ∑ i in s , f i . totalDegree := mul_sum.symm
              _ < q - 1 * Fintype.card σ := by rwa [ mul_lt_mul_left hq ]
          show 1 - f i ^ q - 1 . totalDegree ≤ q - 1 * f i . totalDegree
          calc
            1 - f i ^ q - 1 . totalDegree ≤ max ( 1 : MvPolynomial σ K ) . totalDegree f i ^ q - 1 . totalDegree
                :=
                total_degree_sub _ _
              _ ≤ f i ^ q - 1 . totalDegree := by simp only [ max_eq_rightₓ , Nat.zero_leₓ , total_degree_one ]
              _ ≤ q - 1 * f i . totalDegree := total_degree_pow _ _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The Chevalley–Warning theorem.\nLet `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)\nover a finite field of characteristic `p`.\nAssume that the total degree of `f` is less than the cardinality of `σ`.\nThen the number of solutions of `f` is divisible by `p`.\nSee `char_dvd_card_solutions_family` for a version that takes a family of polynomials `f i`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `char_dvd_card_solutions [])
  (Command.declSig
   [(Term.explicitBinder "(" [`p] [":" (termℕ "ℕ")] [] ")")
    (Term.instBinder "[" [] (Term.app `CharP [`K `p]) "]")
    (Term.implicitBinder "{" [`f] [":" (Term.app `MvPolynomial [`σ `K])] "}")
    (Term.explicitBinder "(" [`h] [":" («term_<_» `f.total_degree "<" (Term.app `Fintype.card [`σ]))] [] ")")]
   (Term.typeSpec
    ":"
    (Init.Core.«term_∣_»
     `p
     " ∣ "
     (Term.app
      `Fintype.card
      [(«term{__:_//_}»
        "{"
        `x
        [":" (Term.arrow `σ "→" `K)]
        "//"
        («term_=_» (Term.app `eval [`x `f]) "=" (numLit "0"))
        "}")]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `F
           [(Term.typeSpec ":" (Term.arrow `Unit "→" (Term.app `MvPolynomial [`σ `K])))]
           ":="
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `f)))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_<_»
              (Algebra.BigOperators.Basic.«term∑_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `Unit]))
               ", "
               (Term.proj (Term.app `F [`i]) "." `totalDegree))
              "<"
              (Term.app `Fintype.card [`σ])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.simpa
                 "simpa"
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `Fintype.univ_punit) "," (Tactic.simpLemma [] [] `sum_singleton)] "]"]
                 []
                 ["using" `h])
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [`key []] [] ":=" (Term.app `char_dvd_card_solutions_family [`p `this]))))
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `F)
           ","
           (Tactic.simpLemma [] [] `Fintype.univ_punit)
           ","
           (Tactic.simpLemma [] [] `forall_eq)
           ","
           (Tactic.simpLemma [] [] `mem_singleton)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`key] []))])
        [])
       (group (Tactic.convert "convert" [] `key []) [])])))
   [])
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `F
          [(Term.typeSpec ":" (Term.arrow `Unit "→" (Term.app `MvPolynomial [`σ `K])))]
          ":="
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `f)))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_<_»
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `Unit]))
              ", "
              (Term.proj (Term.app `F [`i]) "." `totalDegree))
             "<"
             (Term.app `Fintype.card [`σ])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simpa
                "simpa"
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `Fintype.univ_punit) "," (Tactic.simpLemma [] [] `sum_singleton)] "]"]
                []
                ["using" `h])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl (Term.haveIdDecl [`key []] [] ":=" (Term.app `char_dvd_card_solutions_family [`p `this]))))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `F)
          ","
          (Tactic.simpLemma [] [] `Fintype.univ_punit)
          ","
          (Tactic.simpLemma [] [] `forall_eq)
          ","
          (Tactic.simpLemma [] [] `mem_singleton)]
         "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`key] []))])
       [])
      (group (Tactic.convert "convert" [] `key []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.convert "convert" [] `key [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `key
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `F)
     ","
     (Tactic.simpLemma [] [] `Fintype.univ_punit)
     ","
     (Tactic.simpLemma [] [] `forall_eq)
     ","
     (Tactic.simpLemma [] [] `mem_singleton)]
    "]"]
   [(Tactic.location "at" (Tactic.locationHyp [`key] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `key
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_singleton
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `forall_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Fintype.univ_punit
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl (Term.haveIdDecl [`key []] [] ":=" (Term.app `char_dvd_card_solutions_family [`p `this]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `char_dvd_card_solutions_family [`p `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `char_dvd_card_solutions_family
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       («term_<_»
        (Algebra.BigOperators.Basic.«term∑_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `Unit]))
         ", "
         (Term.proj (Term.app `F [`i]) "." `totalDegree))
        "<"
        (Term.app `Fintype.card [`σ])))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simpa
           "simpa"
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `Fintype.univ_punit) "," (Tactic.simpLemma [] [] `sum_singleton)] "]"]
           []
           ["using" `h])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simpa
        "simpa"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Fintype.univ_punit) "," (Tactic.simpLemma [] [] `sum_singleton)] "]"]
        []
        ["using" `h])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa
   "simpa"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `Fintype.univ_punit) "," (Tactic.simpLemma [] [] `sum_singleton)] "]"]
   []
   ["using" `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sum_singleton
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Fintype.univ_punit
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_»
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `Unit]))
    ", "
    (Term.proj (Term.app `F [`i]) "." `totalDegree))
   "<"
   (Term.app `Fintype.card [`σ]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Fintype.card [`σ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `σ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fintype.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `Unit]))
   ", "
   (Term.proj (Term.app `F [`i]) "." `totalDegree))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `F [`i]) "." `totalDegree)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `F [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `F [`i]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
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
/--
    The Chevalley–Warning theorem.
    Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
    over a finite field of characteristic `p`.
    Assume that the total degree of `f` is less than the cardinality of `σ`.
    Then the number of solutions of `f` is divisible by `p`.
    See `char_dvd_card_solutions_family` for a version that takes a family of polynomials `f i`. -/
  theorem
    char_dvd_card_solutions
    ( p : ℕ ) [ CharP K p ] { f : MvPolynomial σ K } ( h : f.total_degree < Fintype.card σ )
      : p ∣ Fintype.card { x : σ → K // eval x f = 0 }
    :=
      by
        let F : Unit → MvPolynomial σ K := fun _ => f
          have
            : ∑ i : Unit , F i . totalDegree < Fintype.card σ
              :=
              by simpa only [ Fintype.univ_punit , sum_singleton ] using h
          have key := char_dvd_card_solutions_family p this
          simp only [ F , Fintype.univ_punit , forall_eq , mem_singleton ] at key
          convert key

end FiniteField

