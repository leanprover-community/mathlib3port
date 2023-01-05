/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module data.fintype.card_embedding
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.BigOperators
import Mathbin.Logic.Equiv.Embedding

/-!
# Number of embeddings

This file establishes the cardinality of `α ↪ β` in full generality.
-/


-- mathport name: finset.card
local notation "|" x "|" => Finset.card x

-- mathport name: fintype.card
local notation "‖" x "‖" => Fintype.card x

open Function

open Nat BigOperators

namespace Fintype

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `card_embedding_eq_of_unique [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α `β] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `Unique [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Fintype [`β]) "]")
        (Term.instBinder
         "["
         []
         (Term.app `Fintype [(Function.Logic.Embedding.Basic.«term_↪_» `α " ↪ " `β)])
         "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Data.Fintype.CardEmbedding.fintype.card
          "‖"
          (Function.Logic.Embedding.Basic.«term_↪_» `α " ↪ " `β)
          "‖")
         "="
         (Data.Fintype.CardEmbedding.fintype.card "‖" `β "‖"))))
      (Command.declValSimple ":=" (Term.app `card_congr [`Equiv.uniqueEmbeddingEquivResult]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `card_congr [`Equiv.uniqueEmbeddingEquivResult])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.uniqueEmbeddingEquivResult
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `card_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Data.Fintype.CardEmbedding.fintype.card
        "‖"
        (Function.Logic.Embedding.Basic.«term_↪_» `α " ↪ " `β)
        "‖")
       "="
       (Data.Fintype.CardEmbedding.fintype.card "‖" `β "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Fintype.CardEmbedding.fintype.card "‖" `β "‖")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Fintype.CardEmbedding.fintype.card', expected 'Data.Fintype.CardEmbedding.fintype.card._@.Data.Fintype.CardEmbedding._hyg.517'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  card_embedding_eq_of_unique
  { α β : Type _ } [ Unique α ] [ Fintype β ] [ Fintype α ↪ β ] : ‖ α ↪ β ‖ = ‖ β ‖
  := card_congr Equiv.uniqueEmbeddingEquivResult
#align fintype.card_embedding_eq_of_unique Fintype.card_embedding_eq_of_unique

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `card_embedding_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α `β] [] "}")
        (Term.instBinder "[" [] (Term.app `Fintype [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Fintype [`β]) "]")
        (Term.instBinder
         "["
         []
         (Term.app `Fintype [(Function.Logic.Embedding.Basic.«term_↪_» `α " ↪ " `β)])
         "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Data.Fintype.CardEmbedding.fintype.card
          "‖"
          (Function.Logic.Embedding.Basic.«term_↪_» `α " ↪ " `β)
          "‖")
         "="
         (Term.app
          (Term.proj (Data.Fintype.CardEmbedding.fintype.card "‖" `β "‖") "." `descFactorial)
          [(Data.Fintype.CardEmbedding.fintype.card "‖" `α "‖")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticClassical_
            "classical"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.induction'
                "induction'"
                [(Tactic.casesTarget [] («term‹_›» "‹" (Term.app `Fintype [`α]) "›"))]
                ["using" `Fintype.induction_empty_option]
                ["with"
                 [(Lean.binderIdent `α₁)
                  (Lean.binderIdent `α₂)
                  (Lean.binderIdent `h₂)
                  (Lean.binderIdent `e)
                  (Lean.binderIdent `ih)
                  (Lean.binderIdent `α)
                  (Lean.binderIdent `h)
                  (Lean.binderIdent `ih)]]
                [])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.tacticLetI_
                  "letI"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.app `Fintype.ofEquiv [(Term.hole "_") `e.symm]))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `card_congr
                      [(Term.app `Equiv.embeddingCongr [`e (Term.app `Equiv.refl [`β])])]))
                    ","
                    (Tactic.rwRule [] `ih)
                    ","
                    (Tactic.rwRule [] (Term.app `card_congr [`e]))]
                   "]")
                  [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `card_pempty)
                    ","
                    (Tactic.rwRule [] `Nat.desc_factorial_zero)
                    ","
                    (Tactic.rwRule [] `card_eq_one_iff)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [`embedding.of_is_empty
                    ","
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`x]
                      []
                      "=>"
                      (Term.app `FunLike.ext [(Term.hole "_") (Term.hole "_") `isEmptyElim])))]
                   "⟩"))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `card_option)
                    ","
                    (Tactic.rwRule [] `Nat.desc_factorial_succ)
                    ","
                    (Tactic.rwRule
                     []
                     (Term.app `card_congr [(Term.app `embedding.option_embedding_equiv [`α `β])]))
                    ","
                    (Tactic.rwRule [] `card_sigma)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ih)]
                   "]")
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `Fintype.card_compl_set)
                    ","
                    (Tactic.simpLemma [] [] `Fintype.card_range)
                    ","
                    (Tactic.simpLemma [] [] `Finset.sum_const)
                    ","
                    (Tactic.simpLemma [] [] `Finset.card_univ)
                    ","
                    (Tactic.simpLemma [] [] `smul_eq_mul)
                    ","
                    (Tactic.simpLemma [] [] `mul_comm)]
                   "]"]
                  [])])])))])))
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
         [(Mathlib.Tactic.tacticClassical_
           "classical"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.induction'
               "induction'"
               [(Tactic.casesTarget [] («term‹_›» "‹" (Term.app `Fintype [`α]) "›"))]
               ["using" `Fintype.induction_empty_option]
               ["with"
                [(Lean.binderIdent `α₁)
                 (Lean.binderIdent `α₂)
                 (Lean.binderIdent `h₂)
                 (Lean.binderIdent `e)
                 (Lean.binderIdent `ih)
                 (Lean.binderIdent `α)
                 (Lean.binderIdent `h)
                 (Lean.binderIdent `ih)]]
               [])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Std.Tactic.tacticLetI_
                 "letI"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   []
                   ":="
                   (Term.app `Fintype.ofEquiv [(Term.hole "_") `e.symm]))))
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app
                     `card_congr
                     [(Term.app `Equiv.embeddingCongr [`e (Term.app `Equiv.refl [`β])])]))
                   ","
                   (Tactic.rwRule [] `ih)
                   ","
                   (Tactic.rwRule [] (Term.app `card_congr [`e]))]
                  "]")
                 [])])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `card_pempty)
                   ","
                   (Tactic.rwRule [] `Nat.desc_factorial_zero)
                   ","
                   (Tactic.rwRule [] `card_eq_one_iff)]
                  "]")
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.anonymousCtor
                  "⟨"
                  [`embedding.of_is_empty
                   ","
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`x]
                     []
                     "=>"
                     (Term.app `FunLike.ext [(Term.hole "_") (Term.hole "_") `isEmptyElim])))]
                  "⟩"))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `card_option)
                   ","
                   (Tactic.rwRule [] `Nat.desc_factorial_succ)
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app `card_congr [(Term.app `embedding.option_embedding_equiv [`α `β])]))
                   ","
                   (Tactic.rwRule [] `card_sigma)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ih)]
                  "]")
                 [])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `Fintype.card_compl_set)
                   ","
                   (Tactic.simpLemma [] [] `Fintype.card_range)
                   ","
                   (Tactic.simpLemma [] [] `Finset.sum_const)
                   ","
                   (Tactic.simpLemma [] [] `Finset.card_univ)
                   ","
                   (Tactic.simpLemma [] [] `smul_eq_mul)
                   ","
                   (Tactic.simpLemma [] [] `mul_comm)]
                  "]"]
                 [])])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticClassical_
       "classical"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] («term‹_›» "‹" (Term.app `Fintype [`α]) "›"))]
           ["using" `Fintype.induction_empty_option]
           ["with"
            [(Lean.binderIdent `α₁)
             (Lean.binderIdent `α₂)
             (Lean.binderIdent `h₂)
             (Lean.binderIdent `e)
             (Lean.binderIdent `ih)
             (Lean.binderIdent `α)
             (Lean.binderIdent `h)
             (Lean.binderIdent `ih)]]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.tacticLetI_
             "letI"
             (Term.haveDecl
              (Term.haveIdDecl [] [] ":=" (Term.app `Fintype.ofEquiv [(Term.hole "_") `e.symm]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 `card_congr
                 [(Term.app `Equiv.embeddingCongr [`e (Term.app `Equiv.refl [`β])])]))
               ","
               (Tactic.rwRule [] `ih)
               ","
               (Tactic.rwRule [] (Term.app `card_congr [`e]))]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `card_pempty)
               ","
               (Tactic.rwRule [] `Nat.desc_factorial_zero)
               ","
               (Tactic.rwRule [] `card_eq_one_iff)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [`embedding.of_is_empty
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 (Term.app `FunLike.ext [(Term.hole "_") (Term.hole "_") `isEmptyElim])))]
              "⟩"))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `card_option)
               ","
               (Tactic.rwRule [] `Nat.desc_factorial_succ)
               ","
               (Tactic.rwRule
                []
                (Term.app `card_congr [(Term.app `embedding.option_embedding_equiv [`α `β])]))
               ","
               (Tactic.rwRule [] `card_sigma)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ih)]
              "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Fintype.card_compl_set)
               ","
               (Tactic.simpLemma [] [] `Fintype.card_range)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_const)
               ","
               (Tactic.simpLemma [] [] `Finset.card_univ)
               ","
               (Tactic.simpLemma [] [] `smul_eq_mul)
               ","
               (Tactic.simpLemma [] [] `mul_comm)]
              "]"]
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `card_option)
           ","
           (Tactic.rwRule [] `Nat.desc_factorial_succ)
           ","
           (Tactic.rwRule
            []
            (Term.app `card_congr [(Term.app `embedding.option_embedding_equiv [`α `β])]))
           ","
           (Tactic.rwRule [] `card_sigma)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ih)]
          "]")
         [])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Fintype.card_compl_set)
           ","
           (Tactic.simpLemma [] [] `Fintype.card_range)
           ","
           (Tactic.simpLemma [] [] `Finset.sum_const)
           ","
           (Tactic.simpLemma [] [] `Finset.card_univ)
           ","
           (Tactic.simpLemma [] [] `smul_eq_mul)
           ","
           (Tactic.simpLemma [] [] `mul_comm)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Fintype.card_compl_set)
         ","
         (Tactic.simpLemma [] [] `Fintype.card_range)
         ","
         (Tactic.simpLemma [] [] `Finset.sum_const)
         ","
         (Tactic.simpLemma [] [] `Finset.card_univ)
         ","
         (Tactic.simpLemma [] [] `smul_eq_mul)
         ","
         (Tactic.simpLemma [] [] `mul_comm)]
        "]"]
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
      `smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.card_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.sum_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.card_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.card_compl_set
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `card_option)
         ","
         (Tactic.rwRule [] `Nat.desc_factorial_succ)
         ","
         (Tactic.rwRule
          []
          (Term.app `card_congr [(Term.app `embedding.option_embedding_equiv [`α `β])]))
         ","
         (Tactic.rwRule [] `card_sigma)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ih)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ih
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `card_sigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `card_congr [(Term.app `embedding.option_embedding_equiv [`α `β])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `embedding.option_embedding_equiv [`α `β])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `embedding.option_embedding_equiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `embedding.option_embedding_equiv [`α `β])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `card_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.desc_factorial_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `card_option
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `card_pempty)
           ","
           (Tactic.rwRule [] `Nat.desc_factorial_zero)
           ","
           (Tactic.rwRule [] `card_eq_one_iff)]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [`embedding.of_is_empty
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Term.app `FunLike.ext [(Term.hole "_") (Term.hole "_") `isEmptyElim])))]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`embedding.of_is_empty
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app `FunLike.ext [(Term.hole "_") (Term.hole "_") `isEmptyElim])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`embedding.of_is_empty
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app `FunLike.ext [(Term.hole "_") (Term.hole "_") `isEmptyElim])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app `FunLike.ext [(Term.hole "_") (Term.hole "_") `isEmptyElim])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `FunLike.ext [(Term.hole "_") (Term.hole "_") `isEmptyElim])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `isEmptyElim
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
      `FunLike.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `embedding.of_is_empty
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `card_pempty)
         ","
         (Tactic.rwRule [] `Nat.desc_factorial_zero)
         ","
         (Tactic.rwRule [] `card_eq_one_iff)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `card_eq_one_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.desc_factorial_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `card_pempty
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.tacticLetI_
         "letI"
         (Term.haveDecl
          (Term.haveIdDecl [] [] ":=" (Term.app `Fintype.ofEquiv [(Term.hole "_") `e.symm]))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app
             `card_congr
             [(Term.app `Equiv.embeddingCongr [`e (Term.app `Equiv.refl [`β])])]))
           ","
           (Tactic.rwRule [] `ih)
           ","
           (Tactic.rwRule [] (Term.app `card_congr [`e]))]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `card_congr
           [(Term.app `Equiv.embeddingCongr [`e (Term.app `Equiv.refl [`β])])]))
         ","
         (Tactic.rwRule [] `ih)
         ","
         (Tactic.rwRule [] (Term.app `card_congr [`e]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `card_congr [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `card_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ih
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `card_congr [(Term.app `Equiv.embeddingCongr [`e (Term.app `Equiv.refl [`β])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Equiv.embeddingCongr [`e (Term.app `Equiv.refl [`β])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Equiv.refl [`β])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Equiv.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Equiv.refl [`β]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Equiv.embeddingCongr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Equiv.embeddingCongr [`e (Term.paren "(" (Term.app `Equiv.refl [`β]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `card_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticLetI_
       "letI"
       (Term.haveDecl
        (Term.haveIdDecl [] [] ":=" (Term.app `Fintype.ofEquiv [(Term.hole "_") `e.symm]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fintype.ofEquiv [(Term.hole "_") `e.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.ofEquiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] («term‹_›» "‹" (Term.app `Fintype [`α]) "›"))]
       ["using" `Fintype.induction_empty_option]
       ["with"
        [(Lean.binderIdent `α₁)
         (Lean.binderIdent `α₂)
         (Lean.binderIdent `h₂)
         (Lean.binderIdent `e)
         (Lean.binderIdent `ih)
         (Lean.binderIdent `α)
         (Lean.binderIdent `h)
         (Lean.binderIdent `ih)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term‹_›» "‹" (Term.app `Fintype [`α]) "›")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fintype [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Data.Fintype.CardEmbedding.fintype.card
        "‖"
        (Function.Logic.Embedding.Basic.«term_↪_» `α " ↪ " `β)
        "‖")
       "="
       (Term.app
        (Term.proj (Data.Fintype.CardEmbedding.fintype.card "‖" `β "‖") "." `descFactorial)
        [(Data.Fintype.CardEmbedding.fintype.card "‖" `α "‖")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Data.Fintype.CardEmbedding.fintype.card "‖" `β "‖") "." `descFactorial)
       [(Data.Fintype.CardEmbedding.fintype.card "‖" `α "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Fintype.CardEmbedding.fintype.card', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Fintype.CardEmbedding.fintype.card', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Fintype.CardEmbedding.fintype.card "‖" `α "‖")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Fintype.CardEmbedding.fintype.card', expected 'Data.Fintype.CardEmbedding.fintype.card._@.Data.Fintype.CardEmbedding._hyg.517'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    card_embedding_eq
    { α β } [ Fintype α ] [ Fintype β ] [ Fintype α ↪ β ] : ‖ α ↪ β ‖ = ‖ β ‖ . descFactorial ‖ α ‖
    :=
      by
        classical
          induction' ‹ Fintype α › using Fintype.induction_empty_option with α₁ α₂ h₂ e ih α h ih
            ·
              letI := Fintype.ofEquiv _ e.symm
                rw [ ← card_congr Equiv.embeddingCongr e Equiv.refl β , ih , card_congr e ]
            ·
              rw [ card_pempty , Nat.desc_factorial_zero , card_eq_one_iff ]
                exact ⟨ embedding.of_is_empty , fun x => FunLike.ext _ _ isEmptyElim ⟩
            ·
              rw
                  [
                    card_option
                      ,
                      Nat.desc_factorial_succ
                      ,
                      card_congr embedding.option_embedding_equiv α β
                      ,
                      card_sigma
                      ,
                      ← ih
                    ]
                simp
                  only
                  [
                    Fintype.card_compl_set
                      ,
                      Fintype.card_range
                      ,
                      Finset.sum_const
                      ,
                      Finset.card_univ
                      ,
                      smul_eq_mul
                      ,
                      mul_comm
                    ]
#align fintype.card_embedding_eq Fintype.card_embedding_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `card_embedding_eq_of_infinite [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α `β] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `Infinite [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Fintype [`β]) "]")
        (Term.instBinder
         "["
         []
         (Term.app `Fintype [(Function.Logic.Embedding.Basic.«term_↪_» `α " ↪ " `β)])
         "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Data.Fintype.CardEmbedding.fintype.card
          "‖"
          (Function.Logic.Embedding.Basic.«term_↪_» `α " ↪ " `β)
          "‖")
         "="
         (num "0"))))
      (Command.declValSimple ":=" `card_eq_zero [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `card_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Data.Fintype.CardEmbedding.fintype.card
        "‖"
        (Function.Logic.Embedding.Basic.«term_↪_» `α " ↪ " `β)
        "‖")
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Data.Fintype.CardEmbedding.fintype.card
       "‖"
       (Function.Logic.Embedding.Basic.«term_↪_» `α " ↪ " `β)
       "‖")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Fintype.CardEmbedding.fintype.card', expected 'Data.Fintype.CardEmbedding.fintype.card._@.Data.Fintype.CardEmbedding._hyg.517'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    card_embedding_eq_of_infinite
    { α β : Type _ } [ Infinite α ] [ Fintype β ] [ Fintype α ↪ β ] : ‖ α ↪ β ‖ = 0
    := card_eq_zero
#align fintype.card_embedding_eq_of_infinite Fintype.card_embedding_eq_of_infinite

end Fintype

