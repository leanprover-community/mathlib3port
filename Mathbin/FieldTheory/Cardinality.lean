/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module field_theory.cardinality
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Ulift
import Mathbin.Data.MvPolynomial.Cardinal
import Mathbin.Data.Rat.Denumerable
import Mathbin.FieldTheory.Finite.GaloisField
import Mathbin.Logic.Equiv.TransferInstance
import Mathbin.RingTheory.Localization.Cardinality
import Mathbin.SetTheory.Cardinal.Divisibility
import Mathbin.Data.Nat.Factorization.PrimePow

/-!
# Cardinality of Fields

In this file we show all the possible cardinalities of fields. All infinite cardinals can harbour
a field structure, and so can all types with prime power cardinalities, and this is sharp.

## Main statements

* `fintype.nonempty_field_iff`: A `fintype` can be given a field structure iff its cardinality is a
  prime power.
* `infinite.nonempty_field` : Any infinite type can be endowed a field structure.
* `field.nonempty_iff` : There is a field structure on type iff its cardinality is a prime power.

-/


-- mathport name: «expr‖ ‖»
local notation "‖" x "‖" => Fintype.card x

open Cardinal nonZeroDivisors

universe u

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "A finite field has prime power cardinality. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `Fintype.is_prime_pow_card_of_field [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α] [] "}")
        (Term.instBinder "[" [] (Term.app `Fintype [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Field [`α]) "]")]
       (Term.typeSpec ":" (Term.app `IsPrimePow [(FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] (Term.app `CharP.exists [`α]))]
            []
            ["with" [(Lean.binderIdent `p) (Lean.binderIdent (Term.hole "_"))]])
           []
           (Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hp []]
              []
              ":="
              (Term.app `Fact.mk [(Term.app `CharP.char_is_prime [`α `p])]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `b
              []
              []
              ":="
              (Term.app `IsNoetherian.finsetBasis [(Term.app `Zmod [`p]) `α]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `Module.card_fintype [`b]))
              ","
              (Tactic.rwRule [] `Zmod.card)
              ","
              (Tactic.rwRule [] `is_prime_pow_pow_iff)]
             "]")
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact "exact" (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `IsPrimePow))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `FiniteDimensional.finrank_eq_card_basis [`b]))]
             "]")
            [])
           []
           (Tactic.exact "exact" `finite_dimensional.finrank_pos.ne')])))
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
         [(Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] (Term.app `CharP.exists [`α]))]
           []
           ["with" [(Lean.binderIdent `p) (Lean.binderIdent (Term.hole "_"))]])
          []
          (Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hp []]
             []
             ":="
             (Term.app `Fact.mk [(Term.app `CharP.char_is_prime [`α `p])]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `b
             []
             []
             ":="
             (Term.app `IsNoetherian.finsetBasis [(Term.app `Zmod [`p]) `α]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `Module.card_fintype [`b]))
             ","
             (Tactic.rwRule [] `Zmod.card)
             ","
             (Tactic.rwRule [] `is_prime_pow_pow_iff)]
            "]")
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `IsPrimePow))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `FiniteDimensional.finrank_eq_card_basis [`b]))]
            "]")
           [])
          []
          (Tactic.exact "exact" `finite_dimensional.finrank_pos.ne')])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `finite_dimensional.finrank_pos.ne')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `finite_dimensional.finrank_pos.ne'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `FiniteDimensional.finrank_eq_card_basis [`b]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `FiniteDimensional.finrank_eq_card_basis [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `FiniteDimensional.finrank_eq_card_basis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `IsPrimePow))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `IsPrimePow))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `hp "." (fieldIdx "1")) "." `IsPrimePow)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hp "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
        [(Tactic.rwRule [] (Term.app `Module.card_fintype [`b]))
         ","
         (Tactic.rwRule [] `Zmod.card)
         ","
         (Tactic.rwRule [] `is_prime_pow_pow_iff)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_prime_pow_pow_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Zmod.card
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Module.card_fintype [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Module.card_fintype
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `b
         []
         []
         ":="
         (Term.app `IsNoetherian.finsetBasis [(Term.app `Zmod [`p]) `α]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsNoetherian.finsetBasis [(Term.app `Zmod [`p]) `α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Zmod [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Zmod [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsNoetherian.finsetBasis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticHaveI_
       "haveI"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hp []]
         []
         ":="
         (Term.app `Fact.mk [(Term.app `CharP.char_is_prime [`α `p])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fact.mk [(Term.app `CharP.char_is_prime [`α `p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `CharP.char_is_prime [`α `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `CharP.char_is_prime
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `CharP.char_is_prime [`α `p])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fact.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] (Term.app `CharP.exists [`α]))]
       []
       ["with" [(Lean.binderIdent `p) (Lean.binderIdent (Term.hole "_"))]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `CharP.exists [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `CharP.exists
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `IsPrimePow [(FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Cardinality.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Cardinality.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Cardinality.«term‖_‖»', expected 'FieldTheory.Cardinality.term‖_‖._@.FieldTheory.Cardinality._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- A finite field has prime power cardinality. -/
  theorem
    Fintype.is_prime_pow_card_of_field
    { α } [ Fintype α ] [ Field α ] : IsPrimePow ‖ α ‖
    :=
      by
        cases' CharP.exists α with p _
          haveI hp := Fact.mk CharP.char_is_prime α p
          let b := IsNoetherian.finsetBasis Zmod p α
          rw [ Module.card_fintype b , Zmod.card , is_prime_pow_pow_iff ]
          · exact hp . 1 . IsPrimePow
          rw [ ← FiniteDimensional.finrank_eq_card_basis b ]
          exact finite_dimensional.finrank_pos.ne'
#align fintype.is_prime_pow_card_of_field Fintype.is_prime_pow_card_of_field

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A `fintype` can be given a field structure iff its cardinality is a prime power. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `Fintype.nonempty_field_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α] [] "}") (Term.instBinder "[" [] (Term.app `Fintype [`α]) "]")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (Term.app `Nonempty [(Term.app `Field [`α])])
         "↔"
         (Term.app `IsPrimePow [(FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.anonymousCtor "⟨" [`h] "⟩")]
                []
                "=>"
                `Fintype.is_prime_pow_card_of_field))
              ","
              (Term.hole "_")]
             "⟩"))
           []
           (Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hn)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hα)])
                 [])]
               "⟩"))]
            [])
           []
           (Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Fact.mk [`hp.nat_prime]))))
           []
           (Tactic.exact
            "exact"
            (Term.anonymousCtor
             "⟨"
             [(Term.proj
               (Term.proj
                (Term.app
                 `Fintype.equivOfCardEq
                 [(Term.app
                   (Term.proj (Term.app `GaloisField.card [`p `n `hn.ne']) "." `trans)
                   [`hα])])
                "."
                `symm)
               "."
               `Field)]
             "⟩"))])))
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
         [(Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.anonymousCtor "⟨" [`h] "⟩")]
               []
               "=>"
               `Fintype.is_prime_pow_card_of_field))
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hn)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hα)])
                [])]
              "⟩"))]
           [])
          []
          (Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Fact.mk [`hp.nat_prime]))))
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [(Term.proj
              (Term.proj
               (Term.app
                `Fintype.equivOfCardEq
                [(Term.app
                  (Term.proj (Term.app `GaloisField.card [`p `n `hn.ne']) "." `trans)
                  [`hα])])
               "."
               `symm)
              "."
              `Field)]
            "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.proj
          (Term.proj
           (Term.app
            `Fintype.equivOfCardEq
            [(Term.app (Term.proj (Term.app `GaloisField.card [`p `n `hn.ne']) "." `trans) [`hα])])
           "."
           `symm)
          "."
          `Field)]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.proj
         (Term.proj
          (Term.app
           `Fintype.equivOfCardEq
           [(Term.app (Term.proj (Term.app `GaloisField.card [`p `n `hn.ne']) "." `trans) [`hα])])
          "."
          `symm)
         "."
         `Field)]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        (Term.app
         `Fintype.equivOfCardEq
         [(Term.app (Term.proj (Term.app `GaloisField.card [`p `n `hn.ne']) "." `trans) [`hα])])
        "."
        `symm)
       "."
       `Field)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        `Fintype.equivOfCardEq
        [(Term.app (Term.proj (Term.app `GaloisField.card [`p `n `hn.ne']) "." `trans) [`hα])])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Fintype.equivOfCardEq
       [(Term.app (Term.proj (Term.app `GaloisField.card [`p `n `hn.ne']) "." `trans) [`hα])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `GaloisField.card [`p `n `hn.ne']) "." `trans) [`hα])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hα
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `GaloisField.card [`p `n `hn.ne']) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `GaloisField.card [`p `n `hn.ne'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn.ne'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
      `GaloisField.card
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `GaloisField.card [`p `n `hn.ne'])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `GaloisField.card [`p `n `hn.ne']) ")") "." `trans)
      [`hα])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.equivOfCardEq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Fintype.equivOfCardEq
      [(Term.paren
        "("
        (Term.app
         (Term.proj (Term.paren "(" (Term.app `GaloisField.card [`p `n `hn.ne']) ")") "." `trans)
         [`hα])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticHaveI_
       "haveI"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Fact.mk [`hp.nat_prime]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fact.mk [`hp.nat_prime])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.nat_prime
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fact.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hn)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hα)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.anonymousCtor "⟨" [`h] "⟩")]
           []
           "=>"
           `Fintype.is_prime_pow_card_of_field))
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`h] "⟩")]
          []
          "=>"
          `Fintype.is_prime_pow_card_of_field))
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`h] "⟩")]
        []
        "=>"
        `Fintype.is_prime_pow_card_of_field))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.is_prime_pow_card_of_field
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`h] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (Term.app `Nonempty [(Term.app `Field [`α])])
       "↔"
       (Term.app `IsPrimePow [(FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsPrimePow [(FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Cardinality.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Cardinality.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Cardinality.«term‖_‖»', expected 'FieldTheory.Cardinality.term‖_‖._@.FieldTheory.Cardinality._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- A `fintype` can be given a field structure iff its cardinality is a prime power. -/
  theorem
    Fintype.nonempty_field_iff
    { α } [ Fintype α ] : Nonempty Field α ↔ IsPrimePow ‖ α ‖
    :=
      by
        refine' ⟨ fun ⟨ h ⟩ => Fintype.is_prime_pow_card_of_field , _ ⟩
          rintro ⟨ p , n , hp , hn , hα ⟩
          haveI := Fact.mk hp.nat_prime
          exact ⟨ Fintype.equivOfCardEq GaloisField.card p n hn.ne' . trans hα . symm . Field ⟩
#align fintype.nonempty_field_iff Fintype.nonempty_field_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Fintype.not_is_field_of_card_not_prime_pow [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α] [] "}")
        (Term.instBinder "[" [] (Term.app `Fintype [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Ring [`α]) "]")]
       (Term.typeSpec
        ":"
        (Term.arrow
         («term¬_» "¬" (Term.app `IsPrimePow [(FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")]))
         "→"
         («term¬_» "¬" (Term.app `IsField [`α])))))
      (Command.declValSimple
       ":="
       (Term.app
        `mt
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.app
            (Term.proj `Fintype.nonempty_field_iff "." `mp)
            [(Term.anonymousCtor "⟨" [(Term.proj `h "." `toField)] "⟩")])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mt
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.app
           (Term.proj `Fintype.nonempty_field_iff "." `mp)
           [(Term.anonymousCtor "⟨" [(Term.proj `h "." `toField)] "⟩")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.app
         (Term.proj `Fintype.nonempty_field_iff "." `mp)
         [(Term.anonymousCtor "⟨" [(Term.proj `h "." `toField)] "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Fintype.nonempty_field_iff "." `mp)
       [(Term.anonymousCtor "⟨" [(Term.proj `h "." `toField)] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `h "." `toField)] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `h "." `toField)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Fintype.nonempty_field_iff "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Fintype.nonempty_field_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       («term¬_» "¬" (Term.app `IsPrimePow [(FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")]))
       "→"
       («term¬_» "¬" (Term.app `IsField [`α])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (Term.app `IsField [`α]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsField [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 40 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (some 40, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term¬_» "¬" (Term.app `IsPrimePow [(FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsPrimePow [(FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Cardinality.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Cardinality.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (FieldTheory.Cardinality.«term‖_‖» "‖" `α "‖")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'FieldTheory.Cardinality.«term‖_‖»', expected 'FieldTheory.Cardinality.term‖_‖._@.FieldTheory.Cardinality._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Fintype.not_is_field_of_card_not_prime_pow
  { α } [ Fintype α ] [ Ring α ] : ¬ IsPrimePow ‖ α ‖ → ¬ IsField α
  := mt fun h => Fintype.nonempty_field_iff . mp ⟨ h . toField ⟩
#align fintype.not_is_field_of_card_not_prime_pow Fintype.not_is_field_of_card_not_prime_pow

/-- Any infinite type can be endowed a field structure. -/
theorem Infinite.nonempty_field {α : Type u} [Infinite α] : Nonempty (Field α) :=
  by
  letI K := FractionRing (MvPolynomial α <| ULift.{u} ℚ)
  suffices (#α) = (#K) by
    obtain ⟨e⟩ := Cardinal.eq.1 this
    exact ⟨e.field⟩
  rw [← IsLocalization.card (MvPolynomial α <| ULift.{u} ℚ)⁰ K le_rfl]
  apply le_antisymm
  · refine'
      ⟨⟨fun a => MvPolynomial.monomial (Finsupp.single a 1) (1 : ULift.{u} ℚ), fun x y h => _⟩⟩
    simpa [MvPolynomial.monomial_eq_monomial_iff, Finsupp.single_eq_single_iff] using h
  · simp
#align infinite.nonempty_field Infinite.nonempty_field

/-- There is a field structure on type if and only if its cardinality is a prime power. -/
theorem Field.nonempty_iff {α : Type u} : Nonempty (Field α) ↔ IsPrimePow (#α) :=
  by
  rw [Cardinal.is_prime_pow_iff]
  cases' fintypeOrInfinite α with h h
  ·
    simpa only [Cardinal.mk_fintype, Nat.cast_inj, exists_eq_left',
      (Cardinal.nat_lt_aleph_0 _).not_le, false_or_iff] using Fintype.nonempty_field_iff
  · simpa only [← Cardinal.infinite_iff, h, true_or_iff, iff_true_iff] using Infinite.nonempty_field
#align field.nonempty_iff Field.nonempty_iff

