/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen, Scott Morrison

! This file was ported from Lean 3 source module tactic.converter.apply_congr
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Interactive
import Mathbin.Tactic.Converter.Interactive

/-!
## Introduce the `apply_congr` conv mode tactic.

`apply_congr` will apply congruence lemmas inside `conv` mode.
It is particularly useful when the automatically generated congruence lemmas
are not of the optimal shape. An example, described in the doc-string is
rewriting inside the operand of a `finset.sum`.
-/


open Tactic

namespace Conv.Interactive

open Interactive Interactive.Types Lean.Parser

-- mathport name: parser.optional
local postfix:1024 "?" => optional

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Apply a congruence lemma inside `conv` mode.\n\nWhen called without an argument `apply_congr` will try applying all lemmas marked with `@[congr]`.\nOtherwise `apply_congr e` will apply the lemma `e`.\n\nRecall that a goal that appears as `∣ X` in `conv` mode\nrepresents a goal of `⊢ X = ?m`,\ni.e. an equation with a metavariable for the right hand side.\n\nTo successfully use `apply_congr e`, `e` will need to be an equation\n(possibly after function arguments),\nwhich can be unified with a goal of the form `X = ?m`.\nThe right hand side of `e` will then determine the metavariable,\nand `conv` will subsequently replace `X` with that right hand side.\n\nAs usual, `apply_congr` can create new goals;\nany of these which are _not_ equations with a metavariable on the right hand side\nwill be hard to deal with in `conv` mode.\nThus `apply_congr` automatically calls `intros` on any new goals,\nand fails if they are not then equations.\n\nIn particular it is useful for rewriting inside the operand of a `finset.sum`,\nas it provides an extra hypothesis asserting we are inside the domain.\n\nFor example:\n\n```lean\nexample (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m) :\n  finset.sum S f = finset.sum S g :=\nbegin\n  conv_lhs\n  { -- If we just call `congr` here, in the second goal we're helpless,\n    -- because we are only given the opportunity to rewrite `f`.\n    -- However `apply_congr` uses the appropriate `@[congr]` lemma,\n    -- so we get to rewrite `f x`, in the presence of the crucial `H : x ∈ S` hypothesis.\n    apply_congr,\n    skip,\n    simp [h, H], }\nend\n```\n\nIn the above example, when the `apply_congr` tactic is called it gives the hypothesis `H : x ∈ S`\nwhich is then used to rewrite the `f x` to `g x`.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `apply_congr [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`q]
         [":"
          (Term.app
           `parse
           [(Conv.Interactive.Tactic.Converter.ApplyCongr.parser.optional `texpr "?")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `conv [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl
             `congr_lemmas
             []
             "←"
             (Term.doExpr
              (Term.match
               "match"
               []
               []
               [(Term.matchDiscr [] `q)]
               "with"
               (Term.matchAlts
                [(Term.matchAlt
                  "|"
                  [[(Term.app `some [`e])]]
                  "=>"
                  (Term.do
                   "do"
                   (Term.doSeqIndent
                    [(Term.doSeqItem
                      (Term.doLetArrow "let" [] (Term.doIdDecl `gs [] "←" (Term.doExpr `get_goals)))
                      [])
                     (Term.doSeqItem
                      (Term.doLetArrow
                       "let"
                       []
                       (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `to_expr [`e]))))
                      [])
                     (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
                     (Term.doSeqItem
                      (Term.doExpr (Term.app `return [(«term[_]» "[" [`e] "]")]))
                      [])])))
                 (Term.matchAlt
                  "|"
                  [[`none]]
                  "=>"
                  (Term.do
                   "do"
                   (Term.doSeqIndent
                    [(Term.doSeqItem
                      (Term.doLetArrow
                       "let"
                       []
                       (Term.doIdDecl
                        `congr_lemma_names
                        []
                        "←"
                        (Term.doExpr
                         (Term.app `attribute.get_instances [(Term.quotedName (name "`congr"))]))))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr (Term.app `congr_lemma_names [`mk_const]))
                      [])])))])))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app
             `congr_lemmas
             [(Term.fun
               "fun"
               (Term.basicFun
                [`n]
                []
                "=>"
                (Term.app
                 `seq'
                 [(«term_>>_» (Term.app `tactic.eapply [`n]) ">>" `tactic.skip)
                  («term_>>_»
                   `tactic.intros
                   ">>"
                   (Term.do
                    "do"
                    (Term.doSeqIndent
                     [(Term.doSeqItem
                       (Term.doLetArrow
                        "let"
                        []
                        (Term.doPatDecl
                         (Qq.«termQ(__)»
                          "q("
                          («term_=_» (Term.hole "_") "=" (Term.hole "_"))
                          []
                          ")")
                         "←"
                         (Term.doExpr `target)
                         []))
                       [])
                      (Term.doSeqItem (Term.doExpr `tactic.skip) [])])))])))]))
           [])]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `congr_lemmas
            []
            "←"
            (Term.doExpr
             (Term.match
              "match"
              []
              []
              [(Term.matchDiscr [] `q)]
              "with"
              (Term.matchAlts
               [(Term.matchAlt
                 "|"
                 [[(Term.app `some [`e])]]
                 "=>"
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow "let" [] (Term.doIdDecl `gs [] "←" (Term.doExpr `get_goals)))
                     [])
                    (Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `to_expr [`e]))))
                     [])
                    (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
                    (Term.doSeqItem
                     (Term.doExpr (Term.app `return [(«term[_]» "[" [`e] "]")]))
                     [])])))
                (Term.matchAlt
                 "|"
                 [[`none]]
                 "=>"
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doIdDecl
                       `congr_lemma_names
                       []
                       "←"
                       (Term.doExpr
                        (Term.app `attribute.get_instances [(Term.quotedName (name "`congr"))]))))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr (Term.app `congr_lemma_names [`mk_const]))
                     [])])))])))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `congr_lemmas
            [(Term.fun
              "fun"
              (Term.basicFun
               [`n]
               []
               "=>"
               (Term.app
                `seq'
                [(«term_>>_» (Term.app `tactic.eapply [`n]) ">>" `tactic.skip)
                 («term_>>_»
                  `tactic.intros
                  ">>"
                  (Term.do
                   "do"
                   (Term.doSeqIndent
                    [(Term.doSeqItem
                      (Term.doLetArrow
                       "let"
                       []
                       (Term.doPatDecl
                        (Qq.«termQ(__)» "q(" («term_=_» (Term.hole "_") "=" (Term.hole "_")) [] ")")
                        "←"
                        (Term.doExpr `target)
                        []))
                      [])
                     (Term.doSeqItem (Term.doExpr `tactic.skip) [])])))])))]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_lemmas
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (Term.app
           `seq'
           [(«term_>>_» (Term.app `tactic.eapply [`n]) ">>" `tactic.skip)
            («term_>>_»
             `tactic.intros
             ">>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Qq.«termQ(__)» "q(" («term_=_» (Term.hole "_") "=" (Term.hole "_")) [] ")")
                   "←"
                   (Term.doExpr `target)
                   []))
                 [])
                (Term.doSeqItem (Term.doExpr `tactic.skip) [])])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.app
         `seq'
         [(«term_>>_» (Term.app `tactic.eapply [`n]) ">>" `tactic.skip)
          («term_>>_»
           `tactic.intros
           ">>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Qq.«termQ(__)» "q(" («term_=_» (Term.hole "_") "=" (Term.hole "_")) [] ")")
                 "←"
                 (Term.doExpr `target)
                 []))
               [])
              (Term.doSeqItem (Term.doExpr `tactic.skip) [])])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `seq'
       [(«term_>>_» (Term.app `tactic.eapply [`n]) ">>" `tactic.skip)
        («term_>>_»
         `tactic.intros
         ">>"
         (Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doPatDecl
               (Qq.«termQ(__)» "q(" («term_=_» (Term.hole "_") "=" (Term.hole "_")) [] ")")
               "←"
               (Term.doExpr `target)
               []))
             [])
            (Term.doSeqItem (Term.doExpr `tactic.skip) [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_»
       `tactic.intros
       ">>"
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doPatDecl
             (Qq.«termQ(__)» "q(" («term_=_» (Term.hole "_") "=" (Term.hole "_")) [] ")")
             "←"
             (Term.doExpr `target)
             []))
           [])
          (Term.doSeqItem (Term.doExpr `tactic.skip) [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Qq.«termQ(__)» "q(" («term_=_» (Term.hole "_") "=" (Term.hole "_")) [] ")")
            "←"
            (Term.doExpr `target)
            []))
          [])
         (Term.doSeqItem (Term.doExpr `tactic.skip) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.skip
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `target
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Qq.«termQ(__)» "q(" («term_=_» (Term.hole "_") "=" (Term.hole "_")) [] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      `tactic.intros
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1024, (none, [anonymous]) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 60, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>_»
      `tactic.intros
      ">>"
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Qq.«termQ(__)» "q(" («term_=_» (Term.hole "_") "=" (Term.hole "_")) [] ")")
            "←"
            (Term.doExpr `target)
            []))
          [])
         (Term.doSeqItem (Term.doExpr `tactic.skip) [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_>>_» (Term.app `tactic.eapply [`n]) ">>" `tactic.skip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.skip
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `tactic.eapply [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.eapply
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 60, (some 60, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>_» (Term.app `tactic.eapply [`n]) ">>" `tactic.skip)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `seq'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_lemmas
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `q)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `some [`e])]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow "let" [] (Term.doIdDecl `gs [] "←" (Term.doExpr `get_goals)))
              [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `to_expr [`e]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
             (Term.doSeqItem (Term.doExpr (Term.app `return [(«term[_]» "[" [`e] "]")])) [])])))
         (Term.matchAlt
          "|"
          [[`none]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl
                `congr_lemma_names
                []
                "←"
                (Term.doExpr
                 (Term.app `attribute.get_instances [(Term.quotedName (name "`congr"))]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `congr_lemma_names [`mk_const])) [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `congr_lemma_names
            []
            "←"
            (Term.doExpr (Term.app `attribute.get_instances [(Term.quotedName (name "`congr"))]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `congr_lemma_names [`mk_const])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `congr_lemma_names [`mk_const])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_const
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_lemma_names
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `attribute.get_instances [(Term.quotedName (name "`congr"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`congr"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `attribute.get_instances
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `gs [] "←" (Term.doExpr `get_goals)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `to_expr [`e]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `set_goals [`gs])) [])
         (Term.doSeqItem (Term.doExpr (Term.app `return [(«term[_]» "[" [`e] "]")])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `return [(«term[_]» "[" [`e] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`e] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `set_goals [`gs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set_goals
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `to_expr [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `get_goals
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `conv [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `conv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [(Conv.Interactive.Tactic.Converter.ApplyCongr.parser.optional `texpr "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Conv.Interactive.Tactic.Converter.ApplyCongr.parser.optional', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Conv.Interactive.Tactic.Converter.ApplyCongr.parser.optional', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Conv.Interactive.Tactic.Converter.ApplyCongr.parser.optional `texpr "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Conv.Interactive.Tactic.Converter.ApplyCongr.parser.optional', expected 'Conv.Interactive.Tactic.Converter.ApplyCongr.parser.optional._@.Tactic.Converter.ApplyCongr._hyg.10'
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
/--
      Apply a congruence lemma inside `conv` mode.
      
      When called without an argument `apply_congr` will try applying all lemmas marked with `@[congr]`.
      Otherwise `apply_congr e` will apply the lemma `e`.
      
      Recall that a goal that appears as `∣ X` in `conv` mode
      represents a goal of `⊢ X = ?m`,
      i.e. an equation with a metavariable for the right hand side.
      
      To successfully use `apply_congr e`, `e` will need to be an equation
      (possibly after function arguments),
      which can be unified with a goal of the form `X = ?m`.
      The right hand side of `e` will then determine the metavariable,
      and `conv` will subsequently replace `X` with that right hand side.
      
      As usual, `apply_congr` can create new goals;
      any of these which are _not_ equations with a metavariable on the right hand side
      will be hard to deal with in `conv` mode.
      Thus `apply_congr` automatically calls `intros` on any new goals,
      and fails if they are not then equations.
      
      In particular it is useful for rewriting inside the operand of a `finset.sum`,
      as it provides an extra hypothesis asserting we are inside the domain.
      
      For example:
      
      ```lean
      example (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m) :
        finset.sum S f = finset.sum S g :=
      begin
        conv_lhs
        { -- If we just call `congr` here, in the second goal we're helpless,
          -- because we are only given the opportunity to rewrite `f`.
          -- However `apply_congr` uses the appropriate `@[congr]` lemma,
          -- so we get to rewrite `f x`, in the presence of the crucial `H : x ∈ S` hypothesis.
          apply_congr,
          skip,
          simp [h, H], }
      end
      ```
      
      In the above example, when the `apply_congr` tactic is called it gives the hypothesis `H : x ∈ S`
      which is then used to rewrite the `f x` to `g x`.
      -/
    unsafe
  def
    apply_congr
    ( q : parse texpr ? ) : conv Unit
    :=
      do
        let
            congr_lemmas
              ←
              match
                q
                with
                | some e => do let gs ← get_goals let e ← to_expr e set_goals gs return [ e ]
                  |
                    none
                    =>
                    do
                      let congr_lemma_names ← attribute.get_instances `congr
                        congr_lemma_names mk_const
          congr_lemmas
            fun
              n
                =>
                seq'
                  tactic.eapply n >> tactic.skip
                    tactic.intros >> do let q( _ = _ ) ← target tactic.skip
#align conv.interactive.apply_congr conv.interactive.apply_congr

add_tactic_doc
  { Name := "apply_congr"
    category := DocCategory.tactic
    declNames := [`conv.interactive.apply_congr]
    tags := ["conv", "congruence", "rewriting"] }

end Conv.Interactive

