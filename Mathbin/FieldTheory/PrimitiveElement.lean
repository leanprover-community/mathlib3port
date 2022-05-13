/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathbin.FieldTheory.Adjoin
import Mathbin.FieldTheory.IsAlgClosed.Basic
import Mathbin.FieldTheory.Separable
import Mathbin.RingTheory.IntegralDomain

/-!
# Primitive Element Theorem

In this file we prove the primitive element theorem.

## Main results

- `exists_primitive_element`: a finite separable extension `E / F` has a primitive element, i.e.
  there is an `α : E` such that `F⟮α⟯ = (⊤ : subalgebra F E)`.

## Implementation notes

In declaration names, `primitive_element` abbreviates `adjoin_simple_eq_top`:
it stands for the statement `F⟮α⟯ = (⊤ : subalgebra F E)`. We did not add an extra
declaration `is_primitive_element F α := F⟮α⟯ = (⊤ : subalgebra F E)` because this
requires more unfolding without much obvious benefit.

## Tags

primitive element, separable field extension, separable extension, intermediate field, adjoin,
exists_adjoin_simple_eq_top

-/


noncomputable section

open Classical Polynomial

open FiniteDimensional Polynomial IntermediateField

namespace Field

section PrimitiveElementFinite

variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

/-! ### Primitive element theorem for finite fields -/


-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "**Primitive element theorem** assuming E is finite. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `exists_primitive_element_of_fintype_top [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `Fintype [`E]) "]")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `α)] [":" `E]))
     ","
     («term_=_»
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      "="
      (Order.BoundedOrder.«term⊤» "⊤")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `α)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hα)]) [])]
             "⟩")])]
         []
         [":=" [(Term.app `IsCyclic.exists_generator [(Term.app `Units [`E])])]])
        [])
       (group (Mathlib.Tactic.«tacticUse_,,» "use" [`α]) [])
       (group (Tactic.apply "apply" `eq_top_iff.mpr) [])
       (group
        (Tactic.rintro
         "rintro"
         [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x)) (Tactic.rintroPat.one (Tactic.rcasesPat.clear "-"))]
         [])
        [])
       (group (Tactic.byCases' "by_cases'" [`hx ":"] («term_=_» `x "=" (num "0"))) [])
       (group
        («tactic·.__;_»
         "·"
         [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]") []) [])
          (group
           (Tactic.exact
            "exact"
            (Term.proj
             (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              `F
              "⟮"
              (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
              "⟯")
             "."
             `zero_mem))
           [])])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.obtain
            "obtain"
            [(Tactic.rcasesPatMed
              [(Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
                "⟩")])]
            []
            [":=" [(Term.app `set.mem_range.mp [(Term.app `hα [(Term.app `Units.mk0 [`x `hx])])])]])
           [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.show
                "show"
                («term_=_» `x "=" («term_^_» `α "^" `n))
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.NormCast.tacticNorm_cast__ "norm_cast" []) [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn) "," (Tactic.rwRule [] `Units.coe_mk0)] "]")
                      [])
                     [])])))))]
             "]")
            [])
           [])
          (group
           (Tactic.exact "exact" (Term.app `zpow_mem [(Term.app `mem_adjoin_simple_self [`F (coeNotation "↑" `α)]) `n]))
           [])])
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
     [(group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `α)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hα)]) [])]
            "⟩")])]
        []
        [":=" [(Term.app `IsCyclic.exists_generator [(Term.app `Units [`E])])]])
       [])
      (group (Mathlib.Tactic.«tacticUse_,,» "use" [`α]) [])
      (group (Tactic.apply "apply" `eq_top_iff.mpr) [])
      (group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x)) (Tactic.rintroPat.one (Tactic.rcasesPat.clear "-"))]
        [])
       [])
      (group (Tactic.byCases' "by_cases'" [`hx ":"] («term_=_» `x "=" (num "0"))) [])
      (group
       («tactic·.__;_»
        "·"
        [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]") []) [])
         (group
          (Tactic.exact
           "exact"
           (Term.proj
            (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             `F
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
             "⟯")
            "."
            `zero_mem))
          [])])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.obtain
           "obtain"
           [(Tactic.rcasesPatMed
             [(Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
               "⟩")])]
           []
           [":=" [(Term.app `set.mem_range.mp [(Term.app `hα [(Term.app `Units.mk0 [`x `hx])])])]])
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.show
               "show"
               («term_=_» `x "=" («term_^_» `α "^" `n))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.NormCast.tacticNorm_cast__ "norm_cast" []) [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn) "," (Tactic.rwRule [] `Units.coe_mk0)] "]")
                     [])
                    [])])))))]
            "]")
           [])
          [])
         (group
          (Tactic.exact "exact" (Term.app `zpow_mem [(Term.app `mem_adjoin_simple_self [`F (coeNotation "↑" `α)]) `n]))
          [])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.obtain
      "obtain"
      [(Tactic.rcasesPatMed
        [(Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
          "⟩")])]
      []
      [":=" [(Term.app `set.mem_range.mp [(Term.app `hα [(Term.app `Units.mk0 [`x `hx])])])]])
     [])
    (group
     (Tactic.rwSeq
      "rw"
      []
      (Tactic.rwRuleSeq
       "["
       [(Tactic.rwRule
         []
         (Term.show
          "show"
          («term_=_» `x "=" («term_^_» `α "^" `n))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.NormCast.tacticNorm_cast__ "norm_cast" []) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn) "," (Tactic.rwRule [] `Units.coe_mk0)] "]")
                [])
               [])])))))]
       "]")
      [])
     [])
    (group
     (Tactic.exact "exact" (Term.app `zpow_mem [(Term.app `mem_adjoin_simple_self [`F (coeNotation "↑" `α)]) `n]))
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `zpow_mem [(Term.app `mem_adjoin_simple_self [`F (coeNotation "↑" `α)]) `n]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `zpow_mem [(Term.app `mem_adjoin_simple_self [`F (coeNotation "↑" `α)]) `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `mem_adjoin_simple_self [`F (coeNotation "↑" `α)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (coeNotation "↑" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mem_adjoin_simple_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `mem_adjoin_simple_self [`F (coeNotation "↑" `α)]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `zpow_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.show
       "show"
       («term_=_» `x "=" («term_^_» `α "^" `n))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.NormCast.tacticNorm_cast__ "norm_cast" []) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn) "," (Tactic.rwRule [] `Units.coe_mk0)] "]")
             [])
            [])])))))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.show
   "show"
   («term_=_» `x "=" («term_^_» `α "^" `n))
   (Term.byTactic'
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.NormCast.tacticNorm_cast__ "norm_cast" []) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn) "," (Tactic.rwRule [] `Units.coe_mk0)] "]")
         [])
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn) "," (Tactic.rwRule [] `Units.coe_mk0)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Units.coe_mk0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_» `x "=" («term_^_» `α "^" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» `α "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `α
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.obtain
   "obtain"
   [(Tactic.rcasesPatMed
     [(Tactic.rcasesPat.tuple
       "⟨"
       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
       "⟩")])]
   []
   [":=" [(Term.app `set.mem_range.mp [(Term.app `hα [(Term.app `Units.mk0 [`x `hx])])])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `set.mem_range.mp [(Term.app `hα [(Term.app `Units.mk0 [`x `hx])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hα [(Term.app `Units.mk0 [`x `hx])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Units.mk0 [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Units.mk0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Units.mk0 [`x `hx]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hα
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `hα [(Term.paren "(" [(Term.app `Units.mk0 [`x `hx]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `set.mem_range.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_»
   "·"
   [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]") []) [])
    (group
     (Tactic.exact
      "exact"
      (Term.proj
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")
       "."
       `zero_mem))
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.proj
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    "."
    `zero_mem))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   "."
   `zero_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/-- **Primitive element theorem** assuming E is finite. -/
  theorem
    exists_primitive_element_of_fintype_top
    [ Fintype E ] : ∃ α : E , F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = ⊤
    :=
      by
        obtain ⟨ α , hα ⟩ := IsCyclic.exists_generator Units E
          use α
          apply eq_top_iff.mpr
          rintro x -
          by_cases' hx : x = 0
          · rw [ hx ] exact F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ . zero_mem
          ·
            obtain ⟨ n , hn ⟩ := set.mem_range.mp hα Units.mk0 x hx
              rw [ show x = α ^ n by norm_cast rw [ hn , Units.coe_mk0 ] ]
              exact zpow_mem mem_adjoin_simple_self F ↑ α n

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "Primitive element theorem for finite dimensional extension of a finite field. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `exists_primitive_element_of_fintype_bot [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `Fintype [`F]) "]")
    (Term.instBinder "[" [] (Term.app `FiniteDimensional [`F `E]) "]")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `α)] [":" `E]))
     ","
     («term_=_»
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      "="
      (Order.BoundedOrder.«term⊤» "⊤")))))
  (Command.declValSimple
   ":="
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl [] [(Term.typeSpec ":" (Term.app `Fintype [`E]))] ":=" (Term.app `fintype_of_fintype [`F `E])))
    []
    (Term.app `exists_primitive_element_of_fintype_top [`F `E]))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl [] [(Term.typeSpec ":" (Term.app `Fintype [`E]))] ":=" (Term.app `fintype_of_fintype [`F `E])))
   []
   (Term.app `exists_primitive_element_of_fintype_top [`F `E]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `exists_primitive_element_of_fintype_top [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `exists_primitive_element_of_fintype_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `fintype_of_fintype [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `fintype_of_fintype
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Fintype [`E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fintype
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `α)] [":" `E]))
   ","
   («term_=_»
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    "="
    (Order.BoundedOrder.«term⊤» "⊤")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   "="
   (Order.BoundedOrder.«term⊤» "⊤"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/-- Primitive element theorem for finite dimensional extension of a finite field. -/
  theorem
    exists_primitive_element_of_fintype_bot
    [ Fintype F ] [ FiniteDimensional F E ]
      : ∃ α : E , F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = ⊤
    := have : Fintype E := fintype_of_fintype F E exists_primitive_element_of_fintype_top F E

end PrimitiveElementFinite

/-! ### Primitive element theorem for infinite fields -/


section PrimitiveElementInf

variable {F : Type _} [Field F] [Infinite F] {E : Type _} [Field E] (ϕ : F →+* E) (α β : E)

theorem primitive_element_inf_aux_exists_c (f g : F[X]) :
    ∃ c : F, ∀, ∀ α' ∈ (f.map ϕ).roots, ∀, ∀ β' ∈ (g.map ϕ).roots, ∀, -(α' - α) / (β' - β) ≠ ϕ c := by
  let sf := (f.map ϕ).roots
  let sg := (g.map ϕ).roots
  let s := (sf.bind fun α' => sg.map fun β' => -(α' - α) / (β' - β)).toFinset
  let s' := s.preimage ϕ fun x hx y hy h => ϕ.injective h
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset s'
  simp_rw [Finset.mem_preimage, Multiset.mem_to_finset, Multiset.mem_bind, Multiset.mem_map]  at hc
  push_neg  at hc
  exact ⟨c, hc⟩

variable (F) [Algebra F E]

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `primitive_element_inf_aux [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `IsSeparable [`F `E]) "]")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `γ)] [":" `E]))
     ","
     («term_=_»
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      "="
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [`hα []] [] ":=" (Term.app `IsSeparable.is_integral [`F `α]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [`hβ []] [] ":=" (Term.app `IsSeparable.is_integral [`F `β]))))
        [])
       (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `f [] [] ":=" (Term.app `minpoly [`F `α])))) [])
       (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `g [] [] ":=" (Term.app `minpoly [`F `β])))) [])
       (group
        (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `ιFE [] [] ":=" (Term.app `algebraMap [`F `E]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `ιEE'
           []
           []
           ":="
           (Term.app `algebraMap [`E (Term.app `splitting_field [(Term.app `g.map [`ιFE])])]))))
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hc)]) [])]
             "⟩")])]
         []
         [":="
          [(Term.app
            `primitive_element_inf_aux_exists_c
            [(Term.app `ιEE'.comp [`ιFE]) (Term.app `ιEE' [`α]) (Term.app `ιEE' [`β]) `f `g])]])
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl (Term.letIdDecl `γ [] [] ":=" («term_+_» `α "+" (Algebra.Group.Defs.«term_•_» `c " • " `β)))))
        [])
       (group
        (Mathlib.Tactic.tacticSuffices_
         "suffices"
         [`β_in_Fγ []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            `β
            "∈"
            (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             `F
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
             "⟯")))])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group (Mathlib.Tactic.«tacticUse_,,» "use" [`γ]) [])
          (group (Tactic.apply "apply" `le_antisymmₓ) [])
          (group
           («tactic·.__;_»
            "·"
            [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `adjoin_le_iff)] "]") []) [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`α_in_Fγ []]
                 [(Term.typeSpec
                   ":"
                   («term_∈_»
                    `α
                    "∈"
                    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                     `F
                     "⟮"
                     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                     "⟯")))]
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
                        [(Tactic.rwRule
                          ["←"]
                          (Term.app `add_sub_cancel [`α (Algebra.Group.Defs.«term_•_» `c " • " `β)]))]
                        "]")
                       [])
                      [])
                     (group
                      (Tactic.exact
                       "exact"
                       (Term.app
                        (Term.proj
                         (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                          `F
                          "⟮"
                          (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                          "⟯")
                         "."
                         `sub_mem)
                        [(Term.app `mem_adjoin_simple_self [`F `γ])
                         (Term.app
                          (Term.proj
                           (Term.proj
                            (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                             `F
                             "⟮"
                             (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                             "⟯")
                            "."
                            `toSubalgebra)
                           "."
                           `smul_mem)
                          [`β_in_Fγ `c])]))
                      [])]))))))
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`x `hx] [])]
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.«tactic_<;>_»
                       (Tactic.cases "cases" [(Tactic.casesTarget [] `hx)] [] [])
                       "<;>"
                       (Tactic.«tactic_<;>_»
                        (Tactic.cases "cases" [(Tactic.casesTarget [] `hx)] [] [])
                        "<;>"
                        (Tactic.«tactic_<;>_»
                         (Tactic.cases "cases" [(Tactic.casesTarget [] `hx)] [] [])
                         "<;>"
                         (Tactic.assumption "assumption"))))
                      [])]))))))
              [])])
           [])
          (group
           («tactic·.__;_»
            "·"
            [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `adjoin_le_iff)] "]") []) [])
             (group (Tactic.change "change" («term_⊆_» (Set.«term{_}» "{" [`γ] "}") "⊆" (Term.hole "_")) []) [])
             (group
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.singleton_subset_iff)] "]") [])
              [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`α_in_Fαβ []]
                 [(Term.typeSpec
                   ":"
                   («term_∈_»
                    `α
                    "∈"
                    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                     `F
                     "⟮"
                     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                     "⟯")))]
                 ":="
                 (Term.app
                  `subset_adjoin
                  [`F
                   (Set.«term{_}» "{" [`α "," `β] "}")
                   (Term.app `Set.mem_insert [`α (Set.«term{_}» "{" [`β] "}")])]))))
              [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`β_in_Fαβ []]
                 [(Term.typeSpec
                   ":"
                   («term_∈_»
                    `β
                    "∈"
                    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                     `F
                     "⟮"
                     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                     "⟯")))]
                 ":="
                 (Term.app
                  `subset_adjoin
                  [`F (Set.«term{_}» "{" [`α "," `β] "}") (Term.app `Set.mem_insert_of_mem [`α `rfl])]))))
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.app
                (Term.proj
                 (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `F
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")
                 "."
                 `add_mem)
                [`α_in_Fαβ
                 (Term.app
                  (Term.proj
                   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                    `F
                    "⟮"
                    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                    "⟯")
                   "."
                   `smul_mem)
                  [`β_in_Fαβ])]))
              [])])
           [])])
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `p
           []
           []
           ":="
           (Term.app
            `EuclideanDomain.gcd
            [(Term.app
              (Term.proj
               (Term.app
                `f.map
                [(Term.app
                  `algebraMap
                  [`F
                   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                    `F
                    "⟮"
                    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                    "⟯")])])
               "."
               `comp)
              [(«term_-_»
                (Term.app `C [(Term.app `adjoin_simple.gen [`F `γ])])
                "-"
                («term_*_» (Term.app `C [(coeNotation "↑" `c)]) "*" `X))])
             (Term.app
              `g.map
              [(Term.app
                `algebraMap
                [`F
                 (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `F
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")])])]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `h
           []
           []
           ":="
           (Term.app
            `EuclideanDomain.gcd
            [(Term.app
              (Term.proj (Term.app `f.map [`ιFE]) "." `comp)
              [(«term_-_» (Term.app `C [`γ]) "-" («term_*_» (Term.app `C [(Term.app `ιFE [`c])]) "*" `X))])
             (Term.app `g.map [`ιFE])]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`map_g_ne_zero []]
           [(Term.typeSpec ":" («term_≠_» (Term.app `g.map [`ιFE]) "≠" (num "0")))]
           ":="
           (Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`hβ])]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h_ne_zero []]
           [(Term.typeSpec ":" («term_≠_» `h "≠" (num "0")))]
           ":="
           (Term.app
            `mt
            [`euclidean_domain.gcd_eq_zero_iff.mp
             (Term.app
              `not_and.mpr
              [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `map_g_ne_zero))])]))))
        [])
       (group
        (Mathlib.Tactic.tacticSuffices_
         "suffices"
         [`p_linear []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app
             `p.map
             [(Term.app
               `algebraMap
               [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `F
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")
                `E])])
            "="
            («term_*_» (Term.app `C [`h.leading_coeff]) "*" («term_-_» `X "-" (Term.app `C [`β])))))])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`finale []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 `β
                 "="
                 (Term.app
                  `algebraMap
                  [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                    `F
                    "⟮"
                    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                    "⟯")
                   `E
                   («term_/_» («term-_» "-" (Term.app `p.coeff [(num "0")])) "/" (Term.app `p.coeff [(num "1")]))])))]
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
                     [(Tactic.rwRule [] `RingHom.map_div)
                      ","
                      (Tactic.rwRule [] `RingHom.map_neg)
                      ","
                      (Tactic.rwRule ["←"] `coeff_map)
                      ","
                      (Tactic.rwRule ["←"] `coeff_map)
                      ","
                      (Tactic.rwRule [] `p_linear)]
                     "]")
                    [])
                   [])
                  (group
                   (Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["["
                     [(Tactic.simpLemma [] [] `mul_sub)
                      ","
                      (Tactic.simpLemma [] [] `coeff_C)
                      ","
                      (Tactic.simpLemma
                       []
                       []
                       (Term.app `mul_div_cancel_left [`β (Term.app `mt [`leading_coeff_eq_zero.mp `h_ne_zero])]))]
                     "]"]
                    [])
                   [])]))))))
           [])
          (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `finale)] "]") []) [])
          (group
           (Tactic.exact
            "exact"
            (Term.app
             `Subtype.mem
             [(«term_/_» («term-_» "-" (Term.app `p.coeff [(num "0")])) "/" (Term.app `p.coeff [(num "1")]))]))
           [])])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h_sep []]
           [(Term.typeSpec ":" `h.separable)]
           ":="
           (Term.app
            `separable_gcd_right
            [(Term.hole "_") (Term.proj (Term.app `IsSeparable.separable [`F `β]) "." `map)]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h_root []]
           [(Term.typeSpec ":" («term_=_» (Term.app `h.eval [`β]) "=" (num "0")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.apply "apply" `eval_gcd_eq_zero) [])
               (group
                («tactic·.__;_»
                 "·"
                 [(group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `eval_comp)
                      ","
                      (Tactic.rwRule [] `eval_sub)
                      ","
                      (Tactic.rwRule [] `eval_mul)
                      ","
                      (Tactic.rwRule [] `eval_C)
                      ","
                      (Tactic.rwRule [] `eval_C)
                      ","
                      (Tactic.rwRule [] `eval_X)
                      ","
                      (Tactic.rwRule [] `eval_map)
                      ","
                      (Tactic.rwRule ["←"] `aeval_def)
                      ","
                      (Tactic.rwRule ["←"] `Algebra.smul_def)
                      ","
                      (Tactic.rwRule [] `add_sub_cancel)
                      ","
                      (Tactic.rwRule [] `minpoly.aeval)]
                     "]")
                    [])
                   [])])
                [])
               (group
                («tactic·.__;_»
                 "·"
                 [(group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `eval_map)
                      ","
                      (Tactic.rwRule ["←"] `aeval_def)
                      ","
                      (Tactic.rwRule [] `minpoly.aeval)]
                     "]")
                    [])
                   [])])
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h_splits []]
           [(Term.typeSpec ":" (Term.app `splits [`ιEE' `h]))]
           ":="
           (Term.app
            `splits_of_splits_gcd_right
            [`ιEE' `map_g_ne_zero (Term.app `splitting_field.splits [(Term.hole "_")])]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h_roots []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              []
              ","
              (Mathlib.ExtendedBinder.«term∀__,_»
               "∀"
               (Lean.binderIdent `x)
               («binderTerm∈_» "∈" (Term.proj (Term.app `h.map [`ιEE']) "." `roots))
               ","
               (Term.forall "∀" [] "," («term_=_» `x "=" (Term.app `ιEE' [`β]))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`x `hx]) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mem_roots_map [`h_ne_zero]))] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                [])
               (group
                (Tactic.specialize
                 "specialize"
                 (Term.app
                  `hc
                  [(«term_-_» (Term.app `ιEE' [`γ]) "-" («term_*_» (Term.app `ιEE' [(Term.app `ιFE [`c])]) "*" `x))
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl (Term.haveIdDecl [`f_root []] [] ":=" (Term.app `root_left_of_root_gcd [`hx]))))
                        [])
                       (group
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `eval₂_comp)
                           ","
                           (Tactic.rwRule [] `eval₂_sub)
                           ","
                           (Tactic.rwRule [] `eval₂_mul)
                           ","
                           (Tactic.rwRule [] `eval₂_C)
                           ","
                           (Tactic.rwRule [] `eval₂_C)
                           ","
                           (Tactic.rwRule [] `eval₂_X)
                           ","
                           (Tactic.rwRule [] `eval₂_map)]
                          "]")
                         [(Tactic.location "at" (Tactic.locationHyp [`f_root] []))])
                        [])
                       (group
                        (Tactic.exact
                         "exact"
                         (Term.app
                          (Term.proj (Term.app `mem_roots_map [(Term.app `minpoly.ne_zero [`hα])]) "." `mpr)
                          [`f_root]))
                        [])])))]))
                [])
               (group
                (Tactic.specialize
                 "specialize"
                 (Term.app
                  `hc
                  [`x
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
                          [(Tactic.rwRule [] (Term.app `mem_roots_map [(Term.app `minpoly.ne_zero [`hβ])]))
                           ","
                           (Tactic.rwRule ["←"] `eval₂_map)]
                          "]")
                         [])
                        [])
                       (group (Tactic.exact "exact" (Term.app `root_right_of_root_gcd [`hx])) [])])))]))
                [])
               (group (byContra "by_contra" [`a]) [])
               (group (Tactic.apply "apply" `hc) [])
               (group
                (Tactic.apply "apply" (Term.proj (Term.app `div_eq_iff [(Term.app `sub_ne_zero.mpr [`a])]) "." `mpr))
                [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `Algebra.smul_def)
                   ","
                   (Tactic.simpLemma [] [] `RingHom.map_add)
                   ","
                   (Tactic.simpLemma [] [] `RingHom.map_mul)
                   ","
                   (Tactic.simpLemma [] [] `RingHom.comp_apply)]
                  "]"]
                 [])
                [])
               (group (Tactic.Ring.tacticRing "ring") [])]))))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule ["←"] (Term.app `eq_X_sub_C_of_separable_of_root_eq [`h_sep `h_root `h_splits `h_roots]))]
          "]")
         [])
        [])
       (group
        (Tactic.trans
         "trans"
         [(Term.app
           `EuclideanDomain.gcd
           [(Term.paren
             "("
             [(Term.hole "_") [(Term.typeAscription ":" (Polynomial.Data.Polynomial.Basic.«term_[X]» `E "[X]"))]]
             ")")
            (Term.paren
             "("
             [(Term.hole "_") [(Term.typeAscription ":" (Polynomial.Data.Polynomial.Basic.«term_[X]» `E "[X]"))]]
             ")")])])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group (Tactic.dsimp' "dsimp'" [] ["only"] ["[" [(Tactic.simpLemma [] [] `p)] "]"] [] []) [])
          (group
           (Tactic.convert
            "convert"
            []
            (Term.proj
             (Term.app
              `gcd_map
              [(Term.app
                `algebraMap
                [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `F
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")
                 `E])])
             "."
             `symm)
            [])
           [])])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Mathlib.Tactic.tacticSimpa!?_
            "simpa"
            []
            []
            (Mathlib.Tactic.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `map_comp)
                ","
                (Tactic.simpLemma [] [] `Polynomial.map_map)
                ","
                (Tactic.simpLemma [] ["←"] `IsScalarTower.algebra_map_eq)
                ","
                (Tactic.simpLemma [] [] `h)]
               "]")]
             []
             []))
           [])])
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
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl (Term.haveIdDecl [`hα []] [] ":=" (Term.app `IsSeparable.is_integral [`F `α]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl (Term.haveIdDecl [`hβ []] [] ":=" (Term.app `IsSeparable.is_integral [`F `β]))))
       [])
      (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `f [] [] ":=" (Term.app `minpoly [`F `α])))) [])
      (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `g [] [] ":=" (Term.app `minpoly [`F `β])))) [])
      (group
       (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `ιFE [] [] ":=" (Term.app `algebraMap [`F `E]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `ιEE'
          []
          []
          ":="
          (Term.app `algebraMap [`E (Term.app `splitting_field [(Term.app `g.map [`ιFE])])]))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hc)]) [])]
            "⟩")])]
        []
        [":="
         [(Term.app
           `primitive_element_inf_aux_exists_c
           [(Term.app `ιEE'.comp [`ιFE]) (Term.app `ιEE' [`α]) (Term.app `ιEE' [`β]) `f `g])]])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl (Term.letIdDecl `γ [] [] ":=" («term_+_» `α "+" (Algebra.Group.Defs.«term_•_» `c " • " `β)))))
       [])
      (group
       (Mathlib.Tactic.tacticSuffices_
        "suffices"
        [`β_in_Fγ []]
        [(Term.typeSpec
          ":"
          («term_∈_»
           `β
           "∈"
           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `F
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯")))])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group (Mathlib.Tactic.«tacticUse_,,» "use" [`γ]) [])
         (group (Tactic.apply "apply" `le_antisymmₓ) [])
         (group
          («tactic·.__;_»
           "·"
           [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `adjoin_le_iff)] "]") []) [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`α_in_Fγ []]
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   `α
                   "∈"
                   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                    `F
                    "⟮"
                    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                    "⟯")))]
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
                       [(Tactic.rwRule
                         ["←"]
                         (Term.app `add_sub_cancel [`α (Algebra.Group.Defs.«term_•_» `c " • " `β)]))]
                       "]")
                      [])
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.app
                       (Term.proj
                        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                         `F
                         "⟮"
                         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                         "⟯")
                        "."
                        `sub_mem)
                       [(Term.app `mem_adjoin_simple_self [`F `γ])
                        (Term.app
                         (Term.proj
                          (Term.proj
                           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                            `F
                            "⟮"
                            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                            "⟯")
                           "."
                           `toSubalgebra)
                          "."
                          `smul_mem)
                         [`β_in_Fγ `c])]))
                     [])]))))))
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`x `hx] [])]
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.«tactic_<;>_»
                      (Tactic.cases "cases" [(Tactic.casesTarget [] `hx)] [] [])
                      "<;>"
                      (Tactic.«tactic_<;>_»
                       (Tactic.cases "cases" [(Tactic.casesTarget [] `hx)] [] [])
                       "<;>"
                       (Tactic.«tactic_<;>_»
                        (Tactic.cases "cases" [(Tactic.casesTarget [] `hx)] [] [])
                        "<;>"
                        (Tactic.assumption "assumption"))))
                     [])]))))))
             [])])
          [])
         (group
          («tactic·.__;_»
           "·"
           [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `adjoin_le_iff)] "]") []) [])
            (group (Tactic.change "change" («term_⊆_» (Set.«term{_}» "{" [`γ] "}") "⊆" (Term.hole "_")) []) [])
            (group
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.singleton_subset_iff)] "]") [])
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`α_in_Fαβ []]
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   `α
                   "∈"
                   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                    `F
                    "⟮"
                    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                    "⟯")))]
                ":="
                (Term.app
                 `subset_adjoin
                 [`F
                  (Set.«term{_}» "{" [`α "," `β] "}")
                  (Term.app `Set.mem_insert [`α (Set.«term{_}» "{" [`β] "}")])]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`β_in_Fαβ []]
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   `β
                   "∈"
                   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                    `F
                    "⟮"
                    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                    "⟯")))]
                ":="
                (Term.app
                 `subset_adjoin
                 [`F (Set.«term{_}» "{" [`α "," `β] "}") (Term.app `Set.mem_insert_of_mem [`α `rfl])]))))
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj
                (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `F
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")
                "."
                `add_mem)
               [`α_in_Fαβ
                (Term.app
                 (Term.proj
                  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                   `F
                   "⟮"
                   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                   "⟯")
                  "."
                  `smul_mem)
                 [`β_in_Fαβ])]))
             [])])
          [])])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `p
          []
          []
          ":="
          (Term.app
           `EuclideanDomain.gcd
           [(Term.app
             (Term.proj
              (Term.app
               `f.map
               [(Term.app
                 `algebraMap
                 [`F
                  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                   `F
                   "⟮"
                   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                   "⟯")])])
              "."
              `comp)
             [(«term_-_»
               (Term.app `C [(Term.app `adjoin_simple.gen [`F `γ])])
               "-"
               («term_*_» (Term.app `C [(coeNotation "↑" `c)]) "*" `X))])
            (Term.app
             `g.map
             [(Term.app
               `algebraMap
               [`F
                (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `F
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")])])]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `h
          []
          []
          ":="
          (Term.app
           `EuclideanDomain.gcd
           [(Term.app
             (Term.proj (Term.app `f.map [`ιFE]) "." `comp)
             [(«term_-_» (Term.app `C [`γ]) "-" («term_*_» (Term.app `C [(Term.app `ιFE [`c])]) "*" `X))])
            (Term.app `g.map [`ιFE])]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`map_g_ne_zero []]
          [(Term.typeSpec ":" («term_≠_» (Term.app `g.map [`ιFE]) "≠" (num "0")))]
          ":="
          (Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`hβ])]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_ne_zero []]
          [(Term.typeSpec ":" («term_≠_» `h "≠" (num "0")))]
          ":="
          (Term.app
           `mt
           [`euclidean_domain.gcd_eq_zero_iff.mp
            (Term.app
             `not_and.mpr
             [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `map_g_ne_zero))])]))))
       [])
      (group
       (Mathlib.Tactic.tacticSuffices_
        "suffices"
        [`p_linear []]
        [(Term.typeSpec
          ":"
          («term_=_»
           (Term.app
            `p.map
            [(Term.app
              `algebraMap
              [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                `F
                "⟮"
                (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                "⟯")
               `E])])
           "="
           («term_*_» (Term.app `C [`h.leading_coeff]) "*" («term_-_» `X "-" (Term.app `C [`β])))))])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`finale []]
             [(Term.typeSpec
               ":"
               («term_=_»
                `β
                "="
                (Term.app
                 `algebraMap
                 [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                   `F
                   "⟮"
                   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                   "⟯")
                  `E
                  («term_/_» («term-_» "-" (Term.app `p.coeff [(num "0")])) "/" (Term.app `p.coeff [(num "1")]))])))]
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
                    [(Tactic.rwRule [] `RingHom.map_div)
                     ","
                     (Tactic.rwRule [] `RingHom.map_neg)
                     ","
                     (Tactic.rwRule ["←"] `coeff_map)
                     ","
                     (Tactic.rwRule ["←"] `coeff_map)
                     ","
                     (Tactic.rwRule [] `p_linear)]
                    "]")
                   [])
                  [])
                 (group
                  (Tactic.simp
                   "simp"
                   []
                   []
                   []
                   ["["
                    [(Tactic.simpLemma [] [] `mul_sub)
                     ","
                     (Tactic.simpLemma [] [] `coeff_C)
                     ","
                     (Tactic.simpLemma
                      []
                      []
                      (Term.app `mul_div_cancel_left [`β (Term.app `mt [`leading_coeff_eq_zero.mp `h_ne_zero])]))]
                    "]"]
                   [])
                  [])]))))))
          [])
         (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `finale)] "]") []) [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            `Subtype.mem
            [(«term_/_» («term-_» "-" (Term.app `p.coeff [(num "0")])) "/" (Term.app `p.coeff [(num "1")]))]))
          [])])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_sep []]
          [(Term.typeSpec ":" `h.separable)]
          ":="
          (Term.app
           `separable_gcd_right
           [(Term.hole "_") (Term.proj (Term.app `IsSeparable.separable [`F `β]) "." `map)]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_root []]
          [(Term.typeSpec ":" («term_=_» (Term.app `h.eval [`β]) "=" (num "0")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.apply "apply" `eval_gcd_eq_zero) [])
              (group
               («tactic·.__;_»
                "·"
                [(group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `eval_comp)
                     ","
                     (Tactic.rwRule [] `eval_sub)
                     ","
                     (Tactic.rwRule [] `eval_mul)
                     ","
                     (Tactic.rwRule [] `eval_C)
                     ","
                     (Tactic.rwRule [] `eval_C)
                     ","
                     (Tactic.rwRule [] `eval_X)
                     ","
                     (Tactic.rwRule [] `eval_map)
                     ","
                     (Tactic.rwRule ["←"] `aeval_def)
                     ","
                     (Tactic.rwRule ["←"] `Algebra.smul_def)
                     ","
                     (Tactic.rwRule [] `add_sub_cancel)
                     ","
                     (Tactic.rwRule [] `minpoly.aeval)]
                    "]")
                   [])
                  [])])
               [])
              (group
               («tactic·.__;_»
                "·"
                [(group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `eval_map)
                     ","
                     (Tactic.rwRule ["←"] `aeval_def)
                     ","
                     (Tactic.rwRule [] `minpoly.aeval)]
                    "]")
                   [])
                  [])])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_splits []]
          [(Term.typeSpec ":" (Term.app `splits [`ιEE' `h]))]
          ":="
          (Term.app
           `splits_of_splits_gcd_right
           [`ιEE' `map_g_ne_zero (Term.app `splitting_field.splits [(Term.hole "_")])]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_roots []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             []
             ","
             (Mathlib.ExtendedBinder.«term∀__,_»
              "∀"
              (Lean.binderIdent `x)
              («binderTerm∈_» "∈" (Term.proj (Term.app `h.map [`ιEE']) "." `roots))
              ","
              (Term.forall "∀" [] "," («term_=_» `x "=" (Term.app `ιEE' [`β]))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`x `hx]) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mem_roots_map [`h_ne_zero]))] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
               [])
              (group
               (Tactic.specialize
                "specialize"
                (Term.app
                 `hc
                 [(«term_-_» (Term.app `ιEE' [`γ]) "-" («term_*_» (Term.app `ιEE' [(Term.app `ιFE [`c])]) "*" `x))
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.tacticHave_
                        "have"
                        (Term.haveDecl (Term.haveIdDecl [`f_root []] [] ":=" (Term.app `root_left_of_root_gcd [`hx]))))
                       [])
                      (group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule [] `eval₂_comp)
                          ","
                          (Tactic.rwRule [] `eval₂_sub)
                          ","
                          (Tactic.rwRule [] `eval₂_mul)
                          ","
                          (Tactic.rwRule [] `eval₂_C)
                          ","
                          (Tactic.rwRule [] `eval₂_C)
                          ","
                          (Tactic.rwRule [] `eval₂_X)
                          ","
                          (Tactic.rwRule [] `eval₂_map)]
                         "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`f_root] []))])
                       [])
                      (group
                       (Tactic.exact
                        "exact"
                        (Term.app
                         (Term.proj (Term.app `mem_roots_map [(Term.app `minpoly.ne_zero [`hα])]) "." `mpr)
                         [`f_root]))
                       [])])))]))
               [])
              (group
               (Tactic.specialize
                "specialize"
                (Term.app
                 `hc
                 [`x
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
                         [(Tactic.rwRule [] (Term.app `mem_roots_map [(Term.app `minpoly.ne_zero [`hβ])]))
                          ","
                          (Tactic.rwRule ["←"] `eval₂_map)]
                         "]")
                        [])
                       [])
                      (group (Tactic.exact "exact" (Term.app `root_right_of_root_gcd [`hx])) [])])))]))
               [])
              (group (byContra "by_contra" [`a]) [])
              (group (Tactic.apply "apply" `hc) [])
              (group
               (Tactic.apply "apply" (Term.proj (Term.app `div_eq_iff [(Term.app `sub_ne_zero.mpr [`a])]) "." `mpr))
               [])
              (group
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Algebra.smul_def)
                  ","
                  (Tactic.simpLemma [] [] `RingHom.map_add)
                  ","
                  (Tactic.simpLemma [] [] `RingHom.map_mul)
                  ","
                  (Tactic.simpLemma [] [] `RingHom.comp_apply)]
                 "]"]
                [])
               [])
              (group (Tactic.Ring.tacticRing "ring") [])]))))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] (Term.app `eq_X_sub_C_of_separable_of_root_eq [`h_sep `h_root `h_splits `h_roots]))]
         "]")
        [])
       [])
      (group
       (Tactic.trans
        "trans"
        [(Term.app
          `EuclideanDomain.gcd
          [(Term.paren
            "("
            [(Term.hole "_") [(Term.typeAscription ":" (Polynomial.Data.Polynomial.Basic.«term_[X]» `E "[X]"))]]
            ")")
           (Term.paren
            "("
            [(Term.hole "_") [(Term.typeAscription ":" (Polynomial.Data.Polynomial.Basic.«term_[X]» `E "[X]"))]]
            ")")])])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group (Tactic.dsimp' "dsimp'" [] ["only"] ["[" [(Tactic.simpLemma [] [] `p)] "]"] [] []) [])
         (group
          (Tactic.convert
           "convert"
           []
           (Term.proj
            (Term.app
             `gcd_map
             [(Term.app
               `algebraMap
               [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `F
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")
                `E])])
            "."
            `symm)
           [])
          [])])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Mathlib.Tactic.tacticSimpa!?_
           "simpa"
           []
           []
           (Mathlib.Tactic.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `map_comp)
               ","
               (Tactic.simpLemma [] [] `Polynomial.map_map)
               ","
               (Tactic.simpLemma [] ["←"] `IsScalarTower.algebra_map_eq)
               ","
               (Tactic.simpLemma [] [] `h)]
              "]")]
            []
            []))
          [])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («tactic·.__;_»
   "·"
   [(group
     (Mathlib.Tactic.tacticSimpa!?_
      "simpa"
      []
      []
      (Mathlib.Tactic.simpaArgsRest
       []
       []
       []
       [(Tactic.simpArgs
         "["
         [(Tactic.simpLemma [] [] `map_comp)
          ","
          (Tactic.simpLemma [] [] `Polynomial.map_map)
          ","
          (Tactic.simpLemma [] ["←"] `IsScalarTower.algebra_map_eq)
          ","
          (Tactic.simpLemma [] [] `h)]
         "]")]
       []
       []))
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Mathlib.Tactic.tacticSimpa!?_
   "simpa"
   []
   []
   (Mathlib.Tactic.simpaArgsRest
    []
    []
    []
    [(Tactic.simpArgs
      "["
      [(Tactic.simpLemma [] [] `map_comp)
       ","
       (Tactic.simpLemma [] [] `Polynomial.map_map)
       ","
       (Tactic.simpLemma [] ["←"] `IsScalarTower.algebra_map_eq)
       ","
       (Tactic.simpLemma [] [] `h)]
      "]")]
    []
    []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `IsScalarTower.algebra_map_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Polynomial.map_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `map_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_»
   "·"
   [(group (Tactic.dsimp' "dsimp'" [] ["only"] ["[" [(Tactic.simpLemma [] [] `p)] "]"] [] []) [])
    (group
     (Tactic.convert
      "convert"
      []
      (Term.proj
       (Term.app
        `gcd_map
        [(Term.app
          `algebraMap
          [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `F
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯")
           `E])])
       "."
       `symm)
      [])
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.convert
   "convert"
   []
   (Term.proj
    (Term.app
     `gcd_map
     [(Term.app
       `algebraMap
       [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `F
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")
        `E])])
    "."
    `symm)
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    `gcd_map
    [(Term.app
      `algebraMap
      [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")
       `E])])
   "."
   `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `gcd_map
   [(Term.app
     `algebraMap
     [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      `E])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `algebraMap
   [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  primitive_element_inf_aux
  [ IsSeparable F E ]
    :
      ∃
        γ : E
        ,
        F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
          =
          F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
  :=
    by
      have hα := IsSeparable.is_integral F α
        have hβ := IsSeparable.is_integral F β
        let f := minpoly F α
        let g := minpoly F β
        let ιFE := algebraMap F E
        let ιEE' := algebraMap E splitting_field g.map ιFE
        obtain ⟨ c , hc ⟩ := primitive_element_inf_aux_exists_c ιEE'.comp ιFE ιEE' α ιEE' β f g
        let γ := α + c • β
        suffices β_in_Fγ : β ∈ F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
        ·
          use γ
            apply le_antisymmₓ
            ·
              rw [ adjoin_le_iff ]
                have
                  α_in_Fγ
                    : α ∈ F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                    :=
                    by
                      rw [ ← add_sub_cancel α c • β ]
                        exact
                          F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ . sub_mem
                            mem_adjoin_simple_self F γ
                              F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                                    .
                                    toSubalgebra
                                  .
                                  smul_mem
                                β_in_Fγ c
                exact fun x hx => by cases hx <;> cases hx <;> cases hx <;> assumption
            ·
              rw [ adjoin_le_iff ]
                change { γ } ⊆ _
                rw [ Set.singleton_subset_iff ]
                have
                  α_in_Fαβ
                    : α ∈ F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                    :=
                    subset_adjoin F { α , β } Set.mem_insert α { β }
                have
                  β_in_Fαβ
                    : β ∈ F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                    :=
                    subset_adjoin F { α , β } Set.mem_insert_of_mem α rfl
                exact
                  F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ . add_mem
                    α_in_Fαβ
                      F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ . smul_mem
                        β_in_Fαβ
        let
          p
            :=
            EuclideanDomain.gcd
              f.map algebraMap F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                    .
                    comp
                  C adjoin_simple.gen F γ - C ↑ c * X
                g.map algebraMap F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
        let h := EuclideanDomain.gcd f.map ιFE . comp C γ - C ιFE c * X g.map ιFE
        have map_g_ne_zero : g.map ιFE ≠ 0 := map_ne_zero minpoly.ne_zero hβ
        have h_ne_zero : h ≠ 0 := mt euclidean_domain.gcd_eq_zero_iff.mp not_and.mpr fun _ => map_g_ne_zero
        suffices
          p_linear
          :
            p.map algebraMap F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ E
              =
              C h.leading_coeff * X - C β
        ·
          have
              finale
                :
                  β
                    =
                    algebraMap
                      F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                        E
                        - p.coeff 0 / p.coeff 1
                :=
                by
                  rw [ RingHom.map_div , RingHom.map_neg , ← coeff_map , ← coeff_map , p_linear ]
                    simp [ mul_sub , coeff_C , mul_div_cancel_left β mt leading_coeff_eq_zero.mp h_ne_zero ]
            rw [ finale ]
            exact Subtype.mem - p.coeff 0 / p.coeff 1
        have h_sep : h.separable := separable_gcd_right _ IsSeparable.separable F β . map
        have
          h_root
            : h.eval β = 0
            :=
            by
              apply eval_gcd_eq_zero
                ·
                  rw
                    [
                      eval_comp
                        ,
                        eval_sub
                        ,
                        eval_mul
                        ,
                        eval_C
                        ,
                        eval_C
                        ,
                        eval_X
                        ,
                        eval_map
                        ,
                        ← aeval_def
                        ,
                        ← Algebra.smul_def
                        ,
                        add_sub_cancel
                        ,
                        minpoly.aeval
                      ]
                · rw [ eval_map , ← aeval_def , minpoly.aeval ]
        have h_splits : splits ιEE' h := splits_of_splits_gcd_right ιEE' map_g_ne_zero splitting_field.splits _
        have
          h_roots
            : ∀ , ∀ x ∈ h.map ιEE' . roots , ∀ , x = ιEE' β
            :=
            by
              intro x hx
                rw [ mem_roots_map h_ne_zero ] at hx
                specialize
                  hc
                    ιEE' γ - ιEE' ιFE c * x
                      by
                        have f_root := root_left_of_root_gcd hx
                          rw [ eval₂_comp , eval₂_sub , eval₂_mul , eval₂_C , eval₂_C , eval₂_X , eval₂_map ] at f_root
                          exact mem_roots_map minpoly.ne_zero hα . mpr f_root
                specialize hc x by rw [ mem_roots_map minpoly.ne_zero hβ , ← eval₂_map ] exact root_right_of_root_gcd hx
                by_contra a
                apply hc
                apply div_eq_iff sub_ne_zero.mpr a . mpr
                simp only [ Algebra.smul_def , RingHom.map_add , RingHom.map_mul , RingHom.comp_apply ]
                ring
        rw [ ← eq_X_sub_C_of_separable_of_root_eq h_sep h_root h_splits h_roots ]
        trans EuclideanDomain.gcd ( _ : E [X] ) ( _ : E [X] )
        ·
          dsimp' only [ p ]
            convert
              gcd_map algebraMap F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ E
                .
                symm
        · simpa [ map_comp , Polynomial.map_map , ← IsScalarTower.algebra_map_eq , h ]

end PrimitiveElementInf

variable (F E : Type _) [Field F] [Field E]

variable [Algebra F E] [FiniteDimensional F E]

section SeparableAssumption

variable [IsSeparable F E]

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "Primitive element theorem: a finite separable field extension `E` of `F` has a\n  primitive element, i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : subalgebra F E)`.-/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `exists_primitive_element [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `α)] [":" `E]))
     ","
     («term_=_»
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      "="
      (Order.BoundedOrder.«term⊤» "⊤")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `is_empty_or_nonempty [(Term.app `Fintype [`F])]))]
         ["with"
          (Tactic.rcasesPatLo
           (Tactic.rcasesPatMed
            [(Tactic.rcasesPat.paren
              "("
              (Tactic.rcasesPatLo
               (Tactic.rcasesPatMed
                [(Tactic.rcasesPat.one `F_inf)
                 "|"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo
                    (Tactic.rcasesPatMed
                     [(Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `F_finite)]) [])]
                       "⟩")])
                    [])]
                  "⟩")])
               [])
              ")")])
           [])])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `P
              []
              [(Term.typeSpec ":" (Term.arrow (Term.app `IntermediateField [`F `E]) "→" (Term.prop "Prop")))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`K] [])]
                "=>"
                («term∃_,_»
                 "∃"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `α)] [":" `E]))
                 ","
                 («term_=_»
                  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                   `F
                   "⟮"
                   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                   "⟯")
                  "="
                  `K)))))))
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`base []]
              [(Term.typeSpec ":" (Term.app `P [(Order.BoundedOrder.«term⊥» "⊥")]))]
              ":="
              (Term.anonymousCtor "⟨" [(num "0") "," `adjoin_zero] "⟩"))))
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`ih []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [(Term.simpleBinder [`K] [(Term.typeSpec ":" (Term.app `IntermediateField [`F `E]))])
                  (Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
                 ","
                 (Term.arrow
                  (Term.app `P [`K])
                  "→"
                  (Term.app
                   `P
                   [(coeNotation
                     "↑"
                     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                      `K
                      "⟮"
                      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                      "⟯"))]))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.intro "intro" [`K `β `hK]) [])
                  (group
                   (Tactic.cases'
                    "cases'"
                    [(Tactic.casesTarget [] `hK)]
                    []
                    ["with" [(Lean.binderIdent `α) (Lean.binderIdent `hK)]])
                   [])
                  (group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `hK) "," (Tactic.rwRule [] `adjoin_simple_adjoin_simple)]
                     "]")
                    [])
                   [])
                  (group
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      [(Term.typeSpec ":" (Term.app `Infinite [`F]))]
                      ":="
                      (Term.app `is_empty_fintype.mp [`F_inf]))))
                   [])
                  (group
                   (Tactic.cases'
                    "cases'"
                    [(Tactic.casesTarget [] (Term.app `primitive_element_inf_aux [`F `α `β]))]
                    []
                    ["with" [(Lean.binderIdent `γ) (Lean.binderIdent `hγ)]])
                   [])
                  (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`γ "," `hγ.symm] "⟩")) [])]))))))
           [])
          (group
           (Tactic.exact "exact" (Term.app `induction_on_adjoin [`P `base `ih (Order.BoundedOrder.«term⊤» "⊤")]))
           [])])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group (Tactic.exact "exact" (Term.app `exists_primitive_element_of_fintype_bot [`F `E])) [])])
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
     [(group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `is_empty_or_nonempty [(Term.app `Fintype [`F])]))]
        ["with"
         (Tactic.rcasesPatLo
          (Tactic.rcasesPatMed
           [(Tactic.rcasesPat.paren
             "("
             (Tactic.rcasesPatLo
              (Tactic.rcasesPatMed
               [(Tactic.rcasesPat.one `F_inf)
                "|"
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo
                   (Tactic.rcasesPatMed
                    [(Tactic.rcasesPat.tuple
                      "⟨"
                      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `F_finite)]) [])]
                      "⟩")])
                   [])]
                 "⟩")])
              [])
             ")")])
          [])])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `P
             []
             [(Term.typeSpec ":" (Term.arrow (Term.app `IntermediateField [`F `E]) "→" (Term.prop "Prop")))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`K] [])]
               "=>"
               («term∃_,_»
                "∃"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `α)] [":" `E]))
                ","
                («term_=_»
                 (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `F
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")
                 "="
                 `K)))))))
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`base []]
             [(Term.typeSpec ":" (Term.app `P [(Order.BoundedOrder.«term⊥» "⊥")]))]
             ":="
             (Term.anonymousCtor "⟨" [(num "0") "," `adjoin_zero] "⟩"))))
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`ih []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [(Term.simpleBinder [`K] [(Term.typeSpec ":" (Term.app `IntermediateField [`F `E]))])
                 (Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
                ","
                (Term.arrow
                 (Term.app `P [`K])
                 "→"
                 (Term.app
                  `P
                  [(coeNotation
                    "↑"
                    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                     `K
                     "⟮"
                     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                     "⟯"))]))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.intro "intro" [`K `β `hK]) [])
                 (group
                  (Tactic.cases'
                   "cases'"
                   [(Tactic.casesTarget [] `hK)]
                   []
                   ["with" [(Lean.binderIdent `α) (Lean.binderIdent `hK)]])
                  [])
                 (group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `hK) "," (Tactic.rwRule [] `adjoin_simple_adjoin_simple)]
                    "]")
                   [])
                  [])
                 (group
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec ":" (Term.app `Infinite [`F]))]
                     ":="
                     (Term.app `is_empty_fintype.mp [`F_inf]))))
                  [])
                 (group
                  (Tactic.cases'
                   "cases'"
                   [(Tactic.casesTarget [] (Term.app `primitive_element_inf_aux [`F `α `β]))]
                   []
                   ["with" [(Lean.binderIdent `γ) (Lean.binderIdent `hγ)]])
                  [])
                 (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`γ "," `hγ.symm] "⟩")) [])]))))))
          [])
         (group
          (Tactic.exact "exact" (Term.app `induction_on_adjoin [`P `base `ih (Order.BoundedOrder.«term⊤» "⊤")]))
          [])])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group (Tactic.exact "exact" (Term.app `exists_primitive_element_of_fintype_bot [`F `E])) [])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («tactic·.__;_» "·" [(group (Tactic.exact "exact" (Term.app `exists_primitive_element_of_fintype_bot [`F `E])) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `exists_primitive_element_of_fintype_bot [`F `E]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `exists_primitive_element_of_fintype_bot [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `exists_primitive_element_of_fintype_bot
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.tacticLet_
      "let"
      (Term.letDecl
       (Term.letIdDecl
        `P
        []
        [(Term.typeSpec ":" (Term.arrow (Term.app `IntermediateField [`F `E]) "→" (Term.prop "Prop")))]
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`K] [])]
          "=>"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `α)] [":" `E]))
           ","
           («term_=_»
            (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             `F
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
             "⟯")
            "="
            `K)))))))
     [])
    (group
     (Tactic.tacticHave_
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        [`base []]
        [(Term.typeSpec ":" (Term.app `P [(Order.BoundedOrder.«term⊥» "⊥")]))]
        ":="
        (Term.anonymousCtor "⟨" [(num "0") "," `adjoin_zero] "⟩"))))
     [])
    (group
     (Tactic.tacticHave_
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        [`ih []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           [(Term.simpleBinder [`K] [(Term.typeSpec ":" (Term.app `IntermediateField [`F `E]))])
            (Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
           ","
           (Term.arrow
            (Term.app `P [`K])
            "→"
            (Term.app
             `P
             [(coeNotation
               "↑"
               (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                `K
                "⟮"
                (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                "⟯"))]))))]
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`K `β `hK]) [])
            (group
             (Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] `hK)]
              []
              ["with" [(Lean.binderIdent `α) (Lean.binderIdent `hK)]])
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hK) "," (Tactic.rwRule [] `adjoin_simple_adjoin_simple)] "]")
              [])
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" (Term.app `Infinite [`F]))]
                ":="
                (Term.app `is_empty_fintype.mp [`F_inf]))))
             [])
            (group
             (Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] (Term.app `primitive_element_inf_aux [`F `α `β]))]
              []
              ["with" [(Lean.binderIdent `γ) (Lean.binderIdent `hγ)]])
             [])
            (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`γ "," `hγ.symm] "⟩")) [])]))))))
     [])
    (group (Tactic.exact "exact" (Term.app `induction_on_adjoin [`P `base `ih (Order.BoundedOrder.«term⊤» "⊤")])) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `induction_on_adjoin [`P `base `ih (Order.BoundedOrder.«term⊤» "⊤")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `induction_on_adjoin [`P `base `ih (Order.BoundedOrder.«term⊤» "⊤")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊤»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊤»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `ih
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `base
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `induction_on_adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`ih []]
     [(Term.typeSpec
       ":"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`K] [(Term.typeSpec ":" (Term.app `IntermediateField [`F `E]))])
         (Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
        ","
        (Term.arrow
         (Term.app `P [`K])
         "→"
         (Term.app
          `P
          [(coeNotation
            "↑"
            (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             `K
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
             "⟯"))]))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.intro "intro" [`K `β `hK]) [])
         (group
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `hK)]
           []
           ["with" [(Lean.binderIdent `α) (Lean.binderIdent `hK)]])
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hK) "," (Tactic.rwRule [] `adjoin_simple_adjoin_simple)] "]")
           [])
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `Infinite [`F]))]
             ":="
             (Term.app `is_empty_fintype.mp [`F_inf]))))
          [])
         (group
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] (Term.app `primitive_element_inf_aux [`F `α `β]))]
           []
           ["with" [(Lean.binderIdent `γ) (Lean.binderIdent `hγ)]])
          [])
         (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`γ "," `hγ.symm] "⟩")) [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`K `β `hK]) [])
      (group
       (Tactic.cases' "cases'" [(Tactic.casesTarget [] `hK)] [] ["with" [(Lean.binderIdent `α) (Lean.binderIdent `hK)]])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hK) "," (Tactic.rwRule [] `adjoin_simple_adjoin_simple)] "]")
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" (Term.app `Infinite [`F]))]
          ":="
          (Term.app `is_empty_fintype.mp [`F_inf]))))
       [])
      (group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] (Term.app `primitive_element_inf_aux [`F `α `β]))]
        []
        ["with" [(Lean.binderIdent `γ) (Lean.binderIdent `hγ)]])
       [])
      (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`γ "," `hγ.symm] "⟩")) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`γ "," `hγ.symm] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`γ "," `hγ.symm] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hγ.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `γ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases'
   "cases'"
   [(Tactic.casesTarget [] (Term.app `primitive_element_inf_aux [`F `α `β]))]
   []
   ["with" [(Lean.binderIdent `γ) (Lean.binderIdent `hγ)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `primitive_element_inf_aux [`F `α `β])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `β
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `primitive_element_inf_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl [] [(Term.typeSpec ":" (Term.app `Infinite [`F]))] ":=" (Term.app `is_empty_fintype.mp [`F_inf]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `is_empty_fintype.mp [`F_inf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `F_inf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_empty_fintype.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Infinite [`F])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Infinite
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hK) "," (Tactic.rwRule [] `adjoin_simple_adjoin_simple)] "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `adjoin_simple_adjoin_simple
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hK
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases' "cases'" [(Tactic.casesTarget [] `hK)] [] ["with" [(Lean.binderIdent `α) (Lean.binderIdent `hK)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hK
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`K `β `hK])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hK
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `β
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`K] [(Term.typeSpec ":" (Term.app `IntermediateField [`F `E]))])
    (Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
   ","
   (Term.arrow
    (Term.app `P [`K])
    "→"
    (Term.app
     `P
     [(coeNotation
       "↑"
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `K
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   (Term.app `P [`K])
   "→"
   (Term.app
    `P
    [(coeNotation
      "↑"
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `K
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `P
   [(coeNotation
     "↑"
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `K
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (coeNotation
   "↑"
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `K
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/--
    Primitive element theorem: a finite separable field extension `E` of `F` has a
      primitive element, i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : subalgebra F E)`.-/
  theorem
    exists_primitive_element
    : ∃ α : E , F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = ⊤
    :=
      by
        rcases is_empty_or_nonempty Fintype F with ( F_inf | ⟨ ⟨ F_finite ⟩ ⟩ )
          ·
            let
                P
                  : IntermediateField F E → Prop
                  :=
                  fun
                    K => ∃ α : E , F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = K
              have base : P ⊥ := ⟨ 0 , adjoin_zero ⟩
              have
                ih
                  :
                    ∀
                      K : IntermediateField F E x : E
                      ,
                      P K → P ↑ K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                  :=
                  by
                    intro K β hK
                      cases' hK with α hK
                      rw [ ← hK , adjoin_simple_adjoin_simple ]
                      have : Infinite F := is_empty_fintype.mp F_inf
                      cases' primitive_element_inf_aux F α β with γ hγ
                      exact ⟨ γ , hγ.symm ⟩
              exact induction_on_adjoin P base ih ⊤
          · exact exists_primitive_element_of_fintype_bot F E

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "Alternative phrasing of primitive element theorem:\na finite separable field extension has a basis `1, α, α^2, ..., α^n`.\n\nSee also `exists_primitive_element`. -/")]
  []
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `powerBasisOfFiniteOfSeparable [])
  (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `PowerBasis [`F `E]))])
  (Command.declValSimple
   ":="
   (Term.let
    "let"
    (Term.letDecl (Term.letIdDecl `α [] [] ":=" (Term.proj (Term.app `exists_primitive_element [`F `E]) "." `some)))
    []
    (Term.let
     "let"
     (Term.letDecl
      (Term.letIdDecl `pb [] [] ":=" (Term.app `adjoin.powerBasis [(Term.app `IsSeparable.is_integral [`F `α])])))
     []
     (Term.have
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        [`e []]
        [(Term.typeSpec
          ":"
          («term_=_»
           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `F
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯")
           "="
           (Order.BoundedOrder.«term⊤» "⊤")))]
        ":="
        (Term.proj (Term.app `exists_primitive_element [`F `E]) "." `some_spec)))
      []
      (Term.app
       (Term.proj `pb "." `map)
       [(Term.app
         (Term.proj (Term.app `IntermediateField.equivOfEq [`e]) "." `trans)
         [`IntermediateField.topEquiv])]))))
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl (Term.letIdDecl `α [] [] ":=" (Term.proj (Term.app `exists_primitive_element [`F `E]) "." `some)))
   []
   (Term.let
    "let"
    (Term.letDecl
     (Term.letIdDecl `pb [] [] ":=" (Term.app `adjoin.powerBasis [(Term.app `IsSeparable.is_integral [`F `α])])))
    []
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       [`e []]
       [(Term.typeSpec
         ":"
         («term_=_»
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `F
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")
          "="
          (Order.BoundedOrder.«term⊤» "⊤")))]
       ":="
       (Term.proj (Term.app `exists_primitive_element [`F `E]) "." `some_spec)))
     []
     (Term.app
      (Term.proj `pb "." `map)
      [(Term.app (Term.proj (Term.app `IntermediateField.equivOfEq [`e]) "." `trans) [`IntermediateField.topEquiv])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letIdDecl `pb [] [] ":=" (Term.app `adjoin.powerBasis [(Term.app `IsSeparable.is_integral [`F `α])])))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      [`e []]
      [(Term.typeSpec
        ":"
        («term_=_»
         (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
          `F
          "⟮"
          (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
          "⟯")
         "="
         (Order.BoundedOrder.«term⊤» "⊤")))]
      ":="
      (Term.proj (Term.app `exists_primitive_element [`F `E]) "." `some_spec)))
    []
    (Term.app
     (Term.proj `pb "." `map)
     [(Term.app (Term.proj (Term.app `IntermediateField.equivOfEq [`e]) "." `trans) [`IntermediateField.topEquiv])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`e []]
     [(Term.typeSpec
       ":"
       («term_=_»
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `F
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")
        "="
        (Order.BoundedOrder.«term⊤» "⊤")))]
     ":="
     (Term.proj (Term.app `exists_primitive_element [`F `E]) "." `some_spec)))
   []
   (Term.app
    (Term.proj `pb "." `map)
    [(Term.app (Term.proj (Term.app `IntermediateField.equivOfEq [`e]) "." `trans) [`IntermediateField.topEquiv])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `pb "." `map)
   [(Term.app (Term.proj (Term.app `IntermediateField.equivOfEq [`e]) "." `trans) [`IntermediateField.topEquiv])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `IntermediateField.equivOfEq [`e]) "." `trans) [`IntermediateField.topEquiv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `IntermediateField.topEquiv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `IntermediateField.equivOfEq [`e]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `IntermediateField.equivOfEq [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField.equivOfEq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `IntermediateField.equivOfEq [`e]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj (Term.paren "(" [(Term.app `IntermediateField.equivOfEq [`e]) []] ")") "." `trans)
   [`IntermediateField.topEquiv])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `pb "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `pb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.proj (Term.app `exists_primitive_element [`F `E]) "." `some_spec)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `exists_primitive_element [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `exists_primitive_element
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `exists_primitive_element [`F `E]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   "="
   (Order.BoundedOrder.«term⊤» "⊤"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/--
      Alternative phrasing of primitive element theorem:
      a finite separable field extension has a basis `1, α, α^2, ..., α^n`.
      
      See also `exists_primitive_element`. -/
    noncomputable
  def
    powerBasisOfFiniteOfSeparable
    : PowerBasis F E
    :=
      let
        α := exists_primitive_element F E . some
        let
          pb := adjoin.powerBasis IsSeparable.is_integral F α
          have
            e
              : F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = ⊤
              :=
              exists_primitive_element F E . some_spec
            pb . map IntermediateField.equivOfEq e . trans IntermediateField.topEquiv

end SeparableAssumption

/-- A technical finiteness result. -/
noncomputable def Fintype.subtypeProd {E : Type _} {X : Set E} (hX : X.Finite) {L : Type _} (F : E → Multiset L) :
    Fintype (∀ x : X, { l : L // l ∈ F x }) := by
  classical
  let this : Fintype X := Set.Finite.fintype hX
  exact Pi.fintype

variable (K : Type _) [Field K] [Algebra F K]

variable (E F)

/-- Function from Hom_K(E,L) to pi type Π (x : basis), roots of min poly of x -/
-- Marked as `noncomputable!` since this definition takes multiple seconds to compile,
-- and isn't very computable in practice (since neither `finrank` nor `fin_basis` are).
noncomputable def rootsOfMinPolyPiType (φ : E →ₐ[F] K) (x : Set.Range (FiniteDimensional.finBasis F E : _ → E)) :
    { l : K // l ∈ (((minpoly F x.1).map (algebraMap F K)).roots : Multiset K) } :=
  ⟨φ x, by
    rw [Polynomial.mem_roots_map (minpoly.ne_zero_of_finite_field_extension F x.val), ←
      Polynomial.alg_hom_eval₂_algebra_map, ← φ.map_zero]
    exact congr_argₓ φ (minpoly.aeval F (x : E))⟩

theorem aux_inj_roots_of_min_poly : Function.Injective (rootsOfMinPolyPiType F E K) := by
  intro f g h
  suffices (f : E →ₗ[F] K) = g by
    rw [LinearMap.ext_iff] at this
    ext x
    exact this x
  rw [Function.funext_iffₓ] at h
  apply LinearMap.ext_on (FiniteDimensional.finBasis F E).span_eq
  rintro e he
  have := h ⟨e, he⟩
  apply_fun Subtype.val  at this
  exact this

/-- Given field extensions `E/F` and `K/F`, with `E/F` finite, there are finitely many `F`-algebra
  homomorphisms `E →ₐ[K] K`. -/
noncomputable instance : Fintype (E →ₐ[F] K) := by
  let n := FiniteDimensional.finrank F E
  let B : Basis (Finₓ n) F E := FiniteDimensional.finBasis F E
  let X := Set.Range (B : Finₓ n → E)
  have hX : X.finite := Set.finite_range ⇑B
  refine'
    @Fintype.ofInjective _ _ (fintype.subtype_prod hX fun e => ((minpoly F e).map (algebraMap F K)).roots) _
      (aux_inj_roots_of_min_poly F E K)

end Field

@[simp]
theorem AlgHom.card (F E K : Type _) [Field F] [Field E] [Field K] [IsAlgClosed K] [Algebra F E] [FiniteDimensional F E]
    [IsSeparable F E] [Algebra F K] : Fintype.card (E →ₐ[F] K) = finrank F E := by
  convert
    (AlgHom.card_of_power_basis (Field.powerBasisOfFiniteOfSeparable F E) (IsSeparable.separable _ _)
          (IsAlgClosed.splits_codomain _)).trans
      (PowerBasis.finrank _).symm
  infer_instance

