/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module tactic.simpa
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.DocCommands

open Interactive

open Interactive.Types

namespace Tactic

namespace Interactive

open Expr Lean.Parser

-- mathport name: parser.optional
local postfix:1024 "?" => optional

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This is a \"finishing\" tactic modification of `simp`. It has two forms.\n\n* `simpa [rules, ...] using e` will simplify the goal and the type of\n  `e` using `rules`, then try to close the goal using `e`.\n\n  Simplifying the type of `e` makes it more likely to match the goal\n  (which has also been simplified). This construction also tends to be\n  more robust under changes to the simp lemma set.\n\n* `simpa [rules, ...]` will simplify the goal and the type of a\n  hypothesis `this` if present in the context, then try to close the goal using\n  the `assumption` tactic. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `simpa [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`use_iota_eqn]
         [":"
          («term_<|_»
           `parse
           "<|"
           (Tactic.Interactive.Tactic.Simpa.parser.optional (Term.app `tk [(str "\"!\"")]) "?"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`trace_lemmas]
         [":"
          («term_<|_»
           `parse
           "<|"
           (Tactic.Interactive.Tactic.Simpa.parser.optional (Term.app `tk [(str "\"?\"")]) "?"))]
         []
         ")")
        (Term.explicitBinder "(" [`no_dflt] [":" (Term.app `parse [`only_flag])] [] ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.app `parse [`simp_arg_list])] [] ")")
        (Term.explicitBinder "(" [`attr_names] [":" (Term.app `parse [`with_ident_list])] [] ")")
        (Term.explicitBinder
         "("
         [`tgt]
         [":"
          (Term.app
           `parse
           [(Tactic.Interactive.Tactic.Simpa.parser.optional
             («term_*>_» (Term.app `tk [(str "\"using\"")]) "*>" `texpr)
             "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`cfg]
         [":" `simp_config_ext]
         [(Term.binderDefault ":=" (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}"))]
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.let
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `simp_at
          [(Term.explicitBinder "(" [`lc] [] [] ")")
           (Term.explicitBinder "(" [`close_tac] [":" (Term.app `tactic [`Unit])] [] ")")]
          []
          ":="
          («term_<|_»
           `focus1
           "<|"
           («term_>>_»
            (Term.app
             `simp
             [`use_iota_eqn
              `trace_lemmas
              `no_dflt
              `hs
              `attr_names
              (Term.app `Loc.ns [`lc])
              (Term.structInst
               "{"
               [[`cfg] "with"]
               [(Term.structInstField (Term.structInstLVal `failIfUnchanged []) ":=" `false)]
               (Term.optEllipsis [])
               []
               "}")])
            ">>"
            («term_<|>_»
             («term_>>_» («term_<|>_» `close_tac "<|>" `trivial) ">>" `done)
             "<|>"
             (Term.app `fail [(str "\"simpa failed\"")]))))))
        []
        (Term.match
         "match"
         []
         []
         [(Term.matchDiscr [] `tgt)]
         "with"
         (Term.matchAlts
          [(Term.matchAlt
            "|"
            [[`none]]
            "=>"
            («term_<|>_»
             («term_>>_»
              (Term.app `get_local [(Term.quotedName (name "`this"))])
              ">>"
              (Term.app
               `simp_at
               [(«term[_]» "[" [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none] "]")
                `assumption]))
             "<|>"
             (Term.app `simp_at [(«term[_]» "[" [`none] "]") `assumption])))
           (Term.matchAlt
            "|"
            [[(Term.app `some [`e])]]
            "=>"
            (Term.app
             `focus1
             [(Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl
                    `e
                    []
                    "←"
                    (Term.doExpr
                     («term_<|>_»
                      (Term.app `i_to_expr [`e])
                      "<|>"
                      (Term.do
                       "do"
                       (Term.doSeqIndent
                        [(Term.doSeqItem
                          (Term.doLetArrow
                           "let"
                           []
                           (Term.doIdDecl `ty [] "←" (Term.doExpr `target)))
                          [])
                         (Term.doSeqItem
                          (Term.doLetArrow
                           "let"
                           []
                           (Term.doIdDecl
                            `e
                            []
                            "←"
                            (Term.doExpr
                             (Term.app
                              `i_to_expr_strict
                              [(Term.precheckedQuot
                                "`"
                                (Term.quot
                                 "`("
                                 (Term.typeAscription
                                  "("
                                  (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                                  ":"
                                  [(term.pseudo.antiquot
                                    "$"
                                    []
                                    (antiquotNestedExpr "(" `ty ")")
                                    [])]
                                  ")")
                                 ")"))]))))
                          [])
                         (Term.doSeqItem
                          (Term.doLetArrow
                           "let"
                           []
                           (Term.doIdDecl `pty [] "←" (Term.doExpr (Term.app `pp [`ty]))))
                          [])
                         (Term.doSeqItem
                          (Term.doLetArrow
                           "let"
                           []
                           (Term.doIdDecl `ptgt [] "←" (Term.doExpr (Term.app `pp [`e]))))
                          [])
                         (Term.doSeqItem
                          (Term.doExpr
                           (Term.app
                            `fail
                            [(Term.typeAscription
                              "("
                              («term_++_»
                               («term_++_»
                                («term_++_»
                                 («term_++_»
                                  (str "\"simpa failed, 'using' expression type not directly \"")
                                  "++"
                                  (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
                                 "++"
                                 (Term.app `to_fmt [`pty]))
                                "++"
                                (str "\",\\nfrom \""))
                               "++"
                               `ptgt)
                              ":"
                              [`format]
                              ")")]))
                          [])]))))))
                  [])
                 (Term.doSeqItem
                  (Term.doExpr
                   (Term.match
                    "match"
                    []
                    []
                    [(Term.matchDiscr [] `e)]
                    "with"
                    (Term.matchAlts
                     [(Term.matchAlt
                       "|"
                       [[(Term.app
                          `local_const
                          [(Term.hole "_") `lc (Term.hole "_") (Term.hole "_")])]]
                       "=>"
                       (Term.app
                        `simp_at
                        [(«term[_]» "[" [(Term.app `some [`lc]) "," `none] "]")
                         («term_>>=_» (Term.app `get_local [`lc]) ">>=" `tactic.exact)]))
                      (Term.matchAlt
                       "|"
                       [[`e]]
                       "=>"
                       (Term.do
                        "do"
                        (Term.doSeqIndent
                         [(Term.doSeqItem
                           (Term.doLetArrow
                            "let"
                            []
                            (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                           [])
                          (Term.doSeqItem
                           (Term.doExpr
                            (Term.app `assertv [(Term.quotedName (name "`this")) `t `e]))
                           [])
                          (Term.doSeqItem
                           (Term.doExpr
                            (Term.app
                             `simp_at
                             [(«term[_]»
                               "["
                               [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none]
                               "]")
                              («term_>>=_»
                               (Term.app `get_local [(Term.quotedName (name "`this"))])
                               ">>="
                               `tactic.exact)]))
                           [])
                          (Term.doSeqItem
                           (Term.doExpr (Term.app `all_goals [(Term.app `try [`apply_instance])]))
                           [])])))])))
                  [])]))]))])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `simp_at
         [(Term.explicitBinder "(" [`lc] [] [] ")")
          (Term.explicitBinder "(" [`close_tac] [":" (Term.app `tactic [`Unit])] [] ")")]
         []
         ":="
         («term_<|_»
          `focus1
          "<|"
          («term_>>_»
           (Term.app
            `simp
            [`use_iota_eqn
             `trace_lemmas
             `no_dflt
             `hs
             `attr_names
             (Term.app `Loc.ns [`lc])
             (Term.structInst
              "{"
              [[`cfg] "with"]
              [(Term.structInstField (Term.structInstLVal `failIfUnchanged []) ":=" `false)]
              (Term.optEllipsis [])
              []
              "}")])
           ">>"
           («term_<|>_»
            («term_>>_» («term_<|>_» `close_tac "<|>" `trivial) ">>" `done)
            "<|>"
            (Term.app `fail [(str "\"simpa failed\"")]))))))
       []
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] `tgt)]
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[`none]]
           "=>"
           («term_<|>_»
            («term_>>_»
             (Term.app `get_local [(Term.quotedName (name "`this"))])
             ">>"
             (Term.app
              `simp_at
              [(«term[_]» "[" [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none] "]")
               `assumption]))
            "<|>"
            (Term.app `simp_at [(«term[_]» "[" [`none] "]") `assumption])))
          (Term.matchAlt
           "|"
           [[(Term.app `some [`e])]]
           "=>"
           (Term.app
            `focus1
            [(Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `e
                   []
                   "←"
                   (Term.doExpr
                    («term_<|>_»
                     (Term.app `i_to_expr [`e])
                     "<|>"
                     (Term.do
                      "do"
                      (Term.doSeqIndent
                       [(Term.doSeqItem
                         (Term.doLetArrow "let" [] (Term.doIdDecl `ty [] "←" (Term.doExpr `target)))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl
                           `e
                           []
                           "←"
                           (Term.doExpr
                            (Term.app
                             `i_to_expr_strict
                             [(Term.precheckedQuot
                               "`"
                               (Term.quot
                                "`("
                                (Term.typeAscription
                                 "("
                                 (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                                 ":"
                                 [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                                 ")")
                                ")"))]))))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl `pty [] "←" (Term.doExpr (Term.app `pp [`ty]))))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl `ptgt [] "←" (Term.doExpr (Term.app `pp [`e]))))
                         [])
                        (Term.doSeqItem
                         (Term.doExpr
                          (Term.app
                           `fail
                           [(Term.typeAscription
                             "("
                             («term_++_»
                              («term_++_»
                               («term_++_»
                                («term_++_»
                                 (str "\"simpa failed, 'using' expression type not directly \"")
                                 "++"
                                 (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
                                "++"
                                (Term.app `to_fmt [`pty]))
                               "++"
                               (str "\",\\nfrom \""))
                              "++"
                              `ptgt)
                             ":"
                             [`format]
                             ")")]))
                         [])]))))))
                 [])
                (Term.doSeqItem
                 (Term.doExpr
                  (Term.match
                   "match"
                   []
                   []
                   [(Term.matchDiscr [] `e)]
                   "with"
                   (Term.matchAlts
                    [(Term.matchAlt
                      "|"
                      [[(Term.app
                         `local_const
                         [(Term.hole "_") `lc (Term.hole "_") (Term.hole "_")])]]
                      "=>"
                      (Term.app
                       `simp_at
                       [(«term[_]» "[" [(Term.app `some [`lc]) "," `none] "]")
                        («term_>>=_» (Term.app `get_local [`lc]) ">>=" `tactic.exact)]))
                     (Term.matchAlt
                      "|"
                      [[`e]]
                      "=>"
                      (Term.do
                       "do"
                       (Term.doSeqIndent
                        [(Term.doSeqItem
                          (Term.doLetArrow
                           "let"
                           []
                           (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                          [])
                         (Term.doSeqItem
                          (Term.doExpr (Term.app `assertv [(Term.quotedName (name "`this")) `t `e]))
                          [])
                         (Term.doSeqItem
                          (Term.doExpr
                           (Term.app
                            `simp_at
                            [(«term[_]»
                              "["
                              [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none]
                              "]")
                             («term_>>=_»
                              (Term.app `get_local [(Term.quotedName (name "`this"))])
                              ">>="
                              `tactic.exact)]))
                          [])
                         (Term.doSeqItem
                          (Term.doExpr (Term.app `all_goals [(Term.app `try [`apply_instance])]))
                          [])])))])))
                 [])]))]))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `tgt)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[`none]]
          "=>"
          («term_<|>_»
           («term_>>_»
            (Term.app `get_local [(Term.quotedName (name "`this"))])
            ">>"
            (Term.app
             `simp_at
             [(«term[_]» "[" [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none] "]")
              `assumption]))
           "<|>"
           (Term.app `simp_at [(«term[_]» "[" [`none] "]") `assumption])))
         (Term.matchAlt
          "|"
          [[(Term.app `some [`e])]]
          "=>"
          (Term.app
           `focus1
           [(Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl
                  `e
                  []
                  "←"
                  (Term.doExpr
                   («term_<|>_»
                    (Term.app `i_to_expr [`e])
                    "<|>"
                    (Term.do
                     "do"
                     (Term.doSeqIndent
                      [(Term.doSeqItem
                        (Term.doLetArrow "let" [] (Term.doIdDecl `ty [] "←" (Term.doExpr `target)))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl
                          `e
                          []
                          "←"
                          (Term.doExpr
                           (Term.app
                            `i_to_expr_strict
                            [(Term.precheckedQuot
                              "`"
                              (Term.quot
                               "`("
                               (Term.typeAscription
                                "("
                                (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                                ":"
                                [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                                ")")
                               ")"))]))))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `pty [] "←" (Term.doExpr (Term.app `pp [`ty]))))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `ptgt [] "←" (Term.doExpr (Term.app `pp [`e]))))
                        [])
                       (Term.doSeqItem
                        (Term.doExpr
                         (Term.app
                          `fail
                          [(Term.typeAscription
                            "("
                            («term_++_»
                             («term_++_»
                              («term_++_»
                               («term_++_»
                                (str "\"simpa failed, 'using' expression type not directly \"")
                                "++"
                                (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
                               "++"
                               (Term.app `to_fmt [`pty]))
                              "++"
                              (str "\",\\nfrom \""))
                             "++"
                             `ptgt)
                            ":"
                            [`format]
                            ")")]))
                        [])]))))))
                [])
               (Term.doSeqItem
                (Term.doExpr
                 (Term.match
                  "match"
                  []
                  []
                  [(Term.matchDiscr [] `e)]
                  "with"
                  (Term.matchAlts
                   [(Term.matchAlt
                     "|"
                     [[(Term.app
                        `local_const
                        [(Term.hole "_") `lc (Term.hole "_") (Term.hole "_")])]]
                     "=>"
                     (Term.app
                      `simp_at
                      [(«term[_]» "[" [(Term.app `some [`lc]) "," `none] "]")
                       («term_>>=_» (Term.app `get_local [`lc]) ">>=" `tactic.exact)]))
                    (Term.matchAlt
                     "|"
                     [[`e]]
                     "=>"
                     (Term.do
                      "do"
                      (Term.doSeqIndent
                       [(Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                         [])
                        (Term.doSeqItem
                         (Term.doExpr (Term.app `assertv [(Term.quotedName (name "`this")) `t `e]))
                         [])
                        (Term.doSeqItem
                         (Term.doExpr
                          (Term.app
                           `simp_at
                           [(«term[_]»
                             "["
                             [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none]
                             "]")
                            («term_>>=_»
                             (Term.app `get_local [(Term.quotedName (name "`this"))])
                             ">>="
                             `tactic.exact)]))
                         [])
                        (Term.doSeqItem
                         (Term.doExpr (Term.app `all_goals [(Term.app `try [`apply_instance])]))
                         [])])))])))
                [])]))]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `focus1
       [(Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl
              `e
              []
              "←"
              (Term.doExpr
               («term_<|>_»
                (Term.app `i_to_expr [`e])
                "<|>"
                (Term.do
                 "do"
                 (Term.doSeqIndent
                  [(Term.doSeqItem
                    (Term.doLetArrow "let" [] (Term.doIdDecl `ty [] "←" (Term.doExpr `target)))
                    [])
                   (Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doIdDecl
                      `e
                      []
                      "←"
                      (Term.doExpr
                       (Term.app
                        `i_to_expr_strict
                        [(Term.precheckedQuot
                          "`"
                          (Term.quot
                           "`("
                           (Term.typeAscription
                            "("
                            (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                            ":"
                            [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                            ")")
                           ")"))]))))
                    [])
                   (Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doIdDecl `pty [] "←" (Term.doExpr (Term.app `pp [`ty]))))
                    [])
                   (Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doIdDecl `ptgt [] "←" (Term.doExpr (Term.app `pp [`e]))))
                    [])
                   (Term.doSeqItem
                    (Term.doExpr
                     (Term.app
                      `fail
                      [(Term.typeAscription
                        "("
                        («term_++_»
                         («term_++_»
                          («term_++_»
                           («term_++_»
                            (str "\"simpa failed, 'using' expression type not directly \"")
                            "++"
                            (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
                           "++"
                           (Term.app `to_fmt [`pty]))
                          "++"
                          (str "\",\\nfrom \""))
                         "++"
                         `ptgt)
                        ":"
                        [`format]
                        ")")]))
                    [])]))))))
            [])
           (Term.doSeqItem
            (Term.doExpr
             (Term.match
              "match"
              []
              []
              [(Term.matchDiscr [] `e)]
              "with"
              (Term.matchAlts
               [(Term.matchAlt
                 "|"
                 [[(Term.app `local_const [(Term.hole "_") `lc (Term.hole "_") (Term.hole "_")])]]
                 "=>"
                 (Term.app
                  `simp_at
                  [(«term[_]» "[" [(Term.app `some [`lc]) "," `none] "]")
                   («term_>>=_» (Term.app `get_local [`lc]) ">>=" `tactic.exact)]))
                (Term.matchAlt
                 "|"
                 [[`e]]
                 "=>"
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr (Term.app `assertv [(Term.quotedName (name "`this")) `t `e]))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr
                      (Term.app
                       `simp_at
                       [(«term[_]»
                         "["
                         [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none]
                         "]")
                        («term_>>=_»
                         (Term.app `get_local [(Term.quotedName (name "`this"))])
                         ">>="
                         `tactic.exact)]))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr (Term.app `all_goals [(Term.app `try [`apply_instance])]))
                     [])])))])))
            [])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `e
            []
            "←"
            (Term.doExpr
             («term_<|>_»
              (Term.app `i_to_expr [`e])
              "<|>"
              (Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow "let" [] (Term.doIdDecl `ty [] "←" (Term.doExpr `target)))
                  [])
                 (Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl
                    `e
                    []
                    "←"
                    (Term.doExpr
                     (Term.app
                      `i_to_expr_strict
                      [(Term.precheckedQuot
                        "`"
                        (Term.quot
                         "`("
                         (Term.typeAscription
                          "("
                          (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                          ":"
                          [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                          ")")
                         ")"))]))))
                  [])
                 (Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl `pty [] "←" (Term.doExpr (Term.app `pp [`ty]))))
                  [])
                 (Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl `ptgt [] "←" (Term.doExpr (Term.app `pp [`e]))))
                  [])
                 (Term.doSeqItem
                  (Term.doExpr
                   (Term.app
                    `fail
                    [(Term.typeAscription
                      "("
                      («term_++_»
                       («term_++_»
                        («term_++_»
                         («term_++_»
                          (str "\"simpa failed, 'using' expression type not directly \"")
                          "++"
                          (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
                         "++"
                         (Term.app `to_fmt [`pty]))
                        "++"
                        (str "\",\\nfrom \""))
                       "++"
                       `ptgt)
                      ":"
                      [`format]
                      ")")]))
                  [])]))))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.match
            "match"
            []
            []
            [(Term.matchDiscr [] `e)]
            "with"
            (Term.matchAlts
             [(Term.matchAlt
               "|"
               [[(Term.app `local_const [(Term.hole "_") `lc (Term.hole "_") (Term.hole "_")])]]
               "=>"
               (Term.app
                `simp_at
                [(«term[_]» "[" [(Term.app `some [`lc]) "," `none] "]")
                 («term_>>=_» (Term.app `get_local [`lc]) ">>=" `tactic.exact)]))
              (Term.matchAlt
               "|"
               [[`e]]
               "=>"
               (Term.do
                "do"
                (Term.doSeqIndent
                 [(Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr (Term.app `assertv [(Term.quotedName (name "`this")) `t `e]))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr
                    (Term.app
                     `simp_at
                     [(«term[_]»
                       "["
                       [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none]
                       "]")
                      («term_>>=_»
                       (Term.app `get_local [(Term.quotedName (name "`this"))])
                       ">>="
                       `tactic.exact)]))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr (Term.app `all_goals [(Term.app `try [`apply_instance])]))
                   [])])))])))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `e)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `local_const [(Term.hole "_") `lc (Term.hole "_") (Term.hole "_")])]]
          "=>"
          (Term.app
           `simp_at
           [(«term[_]» "[" [(Term.app `some [`lc]) "," `none] "]")
            («term_>>=_» (Term.app `get_local [`lc]) ">>=" `tactic.exact)]))
         (Term.matchAlt
          "|"
          [[`e]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
              [])
             (Term.doSeqItem
              (Term.doExpr (Term.app `assertv [(Term.quotedName (name "`this")) `t `e]))
              [])
             (Term.doSeqItem
              (Term.doExpr
               (Term.app
                `simp_at
                [(«term[_]» "[" [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none] "]")
                 («term_>>=_»
                  (Term.app `get_local [(Term.quotedName (name "`this"))])
                  ">>="
                  `tactic.exact)]))
              [])
             (Term.doSeqItem
              (Term.doExpr (Term.app `all_goals [(Term.app `try [`apply_instance])]))
              [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
          [])
         (Term.doSeqItem
          (Term.doExpr (Term.app `assertv [(Term.quotedName (name "`this")) `t `e]))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `simp_at
            [(«term[_]» "[" [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none] "]")
             («term_>>=_»
              (Term.app `get_local [(Term.quotedName (name "`this"))])
              ">>="
              `tactic.exact)]))
          [])
         (Term.doSeqItem
          (Term.doExpr (Term.app `all_goals [(Term.app `try [`apply_instance])]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `all_goals [(Term.app `try [`apply_instance])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `try [`apply_instance])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `apply_instance
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `try
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `try [`apply_instance]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `all_goals
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app
       `simp_at
       [(«term[_]» "[" [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none] "]")
        («term_>>=_» (Term.app `get_local [(Term.quotedName (name "`this"))]) ">>=" `tactic.exact)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>=_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>=_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>=_» (Term.app `get_local [(Term.quotedName (name "`this"))]) ">>=" `tactic.exact)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.exact
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `get_local [(Term.quotedName (name "`this"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`this"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_local
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 55, (some 56, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>=_» (Term.app `get_local [(Term.quotedName (name "`this"))]) ">>=" `tactic.exact)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term[_]» "[" [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [(Term.quotedName (name "`this"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`this"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simp_at
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `assertv [(Term.quotedName (name "`this")) `t `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.quotedName (name "`this"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `assertv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `infer_type [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `infer_type
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `simp_at
       [(«term[_]» "[" [(Term.app `some [`lc]) "," `none] "]")
        («term_>>=_» (Term.app `get_local [`lc]) ">>=" `tactic.exact)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>=_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>=_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>=_» (Term.app `get_local [`lc]) ">>=" `tactic.exact)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.exact
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `get_local [`lc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_local
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 55, (some 56, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>=_» (Term.app `get_local [`lc]) ">>=" `tactic.exact)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term[_]» "[" [(Term.app `some [`lc]) "," `none] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`lc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simp_at
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `local_const [(Term.hole "_") `lc (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `lc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `local_const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      («term_<|>_»
       (Term.app `i_to_expr [`e])
       "<|>"
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow "let" [] (Term.doIdDecl `ty [] "←" (Term.doExpr `target)))
           [])
          (Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl
             `e
             []
             "←"
             (Term.doExpr
              (Term.app
               `i_to_expr_strict
               [(Term.precheckedQuot
                 "`"
                 (Term.quot
                  "`("
                  (Term.typeAscription
                   "("
                   (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                   ":"
                   [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                   ")")
                  ")"))]))))
           [])
          (Term.doSeqItem
           (Term.doLetArrow "let" [] (Term.doIdDecl `pty [] "←" (Term.doExpr (Term.app `pp [`ty]))))
           [])
          (Term.doSeqItem
           (Term.doLetArrow "let" [] (Term.doIdDecl `ptgt [] "←" (Term.doExpr (Term.app `pp [`e]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app
             `fail
             [(Term.typeAscription
               "("
               («term_++_»
                («term_++_»
                 («term_++_»
                  («term_++_»
                   (str "\"simpa failed, 'using' expression type not directly \"")
                   "++"
                   (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
                  "++"
                  (Term.app `to_fmt [`pty]))
                 "++"
                 (str "\",\\nfrom \""))
                "++"
                `ptgt)
               ":"
               [`format]
               ")")]))
           [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `ty [] "←" (Term.doExpr `target)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `e
            []
            "←"
            (Term.doExpr
             (Term.app
              `i_to_expr_strict
              [(Term.precheckedQuot
                "`"
                (Term.quot
                 "`("
                 (Term.typeAscription
                  "("
                  (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                  ":"
                  [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                  ")")
                 ")"))]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `pty [] "←" (Term.doExpr (Term.app `pp [`ty]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `ptgt [] "←" (Term.doExpr (Term.app `pp [`e]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `fail
            [(Term.typeAscription
              "("
              («term_++_»
               («term_++_»
                («term_++_»
                 («term_++_»
                  (str "\"simpa failed, 'using' expression type not directly \"")
                  "++"
                  (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
                 "++"
                 (Term.app `to_fmt [`pty]))
                "++"
                (str "\",\\nfrom \""))
               "++"
               `ptgt)
              ":"
              [`format]
              ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `fail
       [(Term.typeAscription
         "("
         («term_++_»
          («term_++_»
           («term_++_»
            («term_++_»
             (str "\"simpa failed, 'using' expression type not directly \"")
             "++"
             (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
            "++"
            (Term.app `to_fmt [`pty]))
           "++"
           (str "\",\\nfrom \""))
          "++"
          `ptgt)
         ":"
         [`format]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_++_»
        («term_++_»
         («term_++_»
          («term_++_»
           (str "\"simpa failed, 'using' expression type not directly \"")
           "++"
           (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
          "++"
          (Term.app `to_fmt [`pty]))
         "++"
         (str "\",\\nfrom \""))
        "++"
        `ptgt)
       ":"
       [`format]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `format
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_»
       («term_++_»
        («term_++_»
         («term_++_»
          (str "\"simpa failed, 'using' expression type not directly \"")
          "++"
          (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
         "++"
         (Term.app `to_fmt [`pty]))
        "++"
        (str "\",\\nfrom \""))
       "++"
       `ptgt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ptgt
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_++_»
       («term_++_»
        («term_++_»
         (str "\"simpa failed, 'using' expression type not directly \"")
         "++"
         (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
        "++"
        (Term.app `to_fmt [`pty]))
       "++"
       (str "\",\\nfrom \""))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\",\\nfrom \"")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_++_»
       («term_++_»
        (str "\"simpa failed, 'using' expression type not directly \"")
        "++"
        (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
       "++"
       (Term.app `to_fmt [`pty]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_fmt [`pty])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pty
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_fmt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_++_»
       (str "\"simpa failed, 'using' expression type not directly \"")
       "++"
       (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \""))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"inferrable. Try:\\n\\nsimpa ... using\\nshow \"")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (str "\"simpa failed, 'using' expression type not directly \"")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fail
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `pp [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `pp [`ty])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ty
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `i_to_expr_strict
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.typeAscription
           "("
           (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
           ":"
           [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
           ")")
          ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.precheckedQuot
       "`"
       (Term.quot
        "`("
        (Term.typeAscription
         "("
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
         ":"
         [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
         ")")
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
       ":"
       [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr_strict
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `target
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.app `i_to_expr [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 1023, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `focus1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<|>_»
       («term_>>_»
        (Term.app `get_local [(Term.quotedName (name "`this"))])
        ">>"
        (Term.app
         `simp_at
         [(«term[_]» "[" [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none] "]")
          `assumption]))
       "<|>"
       (Term.app `simp_at [(«term[_]» "[" [`none] "]") `assumption]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `simp_at [(«term[_]» "[" [`none] "]") `assumption])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `assumption
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term[_]» "[" [`none] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simp_at
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_>>_»
       (Term.app `get_local [(Term.quotedName (name "`this"))])
       ">>"
       (Term.app
        `simp_at
        [(«term[_]» "[" [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none] "]")
         `assumption]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `simp_at
       [(«term[_]» "[" [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none] "]")
        `assumption])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `assumption
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term[_]» "[" [(Term.app `some [(Term.quotedName (name "`this"))]) "," `none] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [(Term.quotedName (name "`this"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`this"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simp_at
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `get_local [(Term.quotedName (name "`this"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`this"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_local
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 60, (some 60, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 20,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tgt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `focus1
       "<|"
       («term_>>_»
        (Term.app
         `simp
         [`use_iota_eqn
          `trace_lemmas
          `no_dflt
          `hs
          `attr_names
          (Term.app `Loc.ns [`lc])
          (Term.structInst
           "{"
           [[`cfg] "with"]
           [(Term.structInstField (Term.structInstLVal `failIfUnchanged []) ":=" `false)]
           (Term.optEllipsis [])
           []
           "}")])
        ">>"
        («term_<|>_»
         («term_>>_» («term_<|>_» `close_tac "<|>" `trivial) ">>" `done)
         "<|>"
         (Term.app `fail [(str "\"simpa failed\"")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_»
       (Term.app
        `simp
        [`use_iota_eqn
         `trace_lemmas
         `no_dflt
         `hs
         `attr_names
         (Term.app `Loc.ns [`lc])
         (Term.structInst
          "{"
          [[`cfg] "with"]
          [(Term.structInstField (Term.structInstLVal `failIfUnchanged []) ":=" `false)]
          (Term.optEllipsis [])
          []
          "}")])
       ">>"
       («term_<|>_»
        («term_>>_» («term_<|>_» `close_tac "<|>" `trivial) ">>" `done)
        "<|>"
        (Term.app `fail [(str "\"simpa failed\"")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|>_»
       («term_>>_» («term_<|>_» `close_tac "<|>" `trivial) ">>" `done)
       "<|>"
       (Term.app `fail [(str "\"simpa failed\"")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fail [(str "\"simpa failed\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"simpa failed\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fail
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_>>_» («term_<|>_» `close_tac "<|>" `trivial) ">>" `done)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `done
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      («term_<|>_» `close_tac "<|>" `trivial)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `trivial
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      `close_tac
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1024, (none, [anonymous]) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 20, (some 20, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|>_» `close_tac "<|>" `trivial)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 21 >? 60, (some 60, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 60 >? 20, (some 20, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|>_»
      («term_>>_» (Term.paren "(" («term_<|>_» `close_tac "<|>" `trivial) ")") ">>" `done)
      "<|>"
      (Term.app `fail [(str "\"simpa failed\"")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app
       `simp
       [`use_iota_eqn
        `trace_lemmas
        `no_dflt
        `hs
        `attr_names
        (Term.app `Loc.ns [`lc])
        (Term.structInst
         "{"
         [[`cfg] "with"]
         [(Term.structInstField (Term.structInstLVal `failIfUnchanged []) ":=" `false)]
         (Term.optEllipsis [])
         []
         "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`cfg] "with"]
       [(Term.structInstField (Term.structInstLVal `failIfUnchanged []) ":=" `false)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `false
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `Loc.ns [`lc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Loc.ns
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Loc.ns [`lc]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `attr_names
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `no_dflt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `trace_lemmas
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `use_iota_eqn
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `focus1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.binderDefault', expected 'Lean.Parser.Term.binderTactic'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simp_config_ext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `parse
       [(Tactic.Interactive.Tactic.Simpa.parser.optional
         («term_*>_» (Term.app `tk [(str "\"using\"")]) "*>" `texpr)
         "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Interactive.Tactic.Simpa.parser.optional', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Interactive.Tactic.Simpa.parser.optional', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.Interactive.Tactic.Simpa.parser.optional
       («term_*>_» (Term.app `tk [(str "\"using\"")]) "*>" `texpr)
       "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Interactive.Tactic.Simpa.parser.optional', expected 'Tactic.Interactive.Tactic.Simpa.parser.optional._@.Tactic.Simpa._hyg.12'
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
      This is a "finishing" tactic modification of `simp`. It has two forms.
      
      * `simpa [rules, ...] using e` will simplify the goal and the type of
        `e` using `rules`, then try to close the goal using `e`.
      
        Simplifying the type of `e` makes it more likely to match the goal
        (which has also been simplified). This construction also tends to be
        more robust under changes to the simp lemma set.
      
      * `simpa [rules, ...]` will simplify the goal and the type of a
        hypothesis `this` if present in the context, then try to close the goal using
        the `assumption` tactic. -/
    unsafe
  def
    simpa
    ( use_iota_eqn : parse <| tk "!" ? )
        ( trace_lemmas : parse <| tk "?" ? )
        ( no_dflt : parse only_flag )
        ( hs : parse simp_arg_list )
        ( attr_names : parse with_ident_list )
        ( tgt : parse tk "using" *> texpr ? )
        ( cfg : simp_config_ext := { } )
      : tactic Unit
    :=
      let
        simp_at
          ( lc ) ( close_tac : tactic Unit )
          :=
          focus1
            <|
            simp
                use_iota_eqn
                  trace_lemmas
                  no_dflt
                  hs
                  attr_names
                  Loc.ns lc
                  { cfg with failIfUnchanged := false }
              >>
              close_tac <|> trivial >> done <|> fail "simpa failed"
        match
          tgt
          with
          |
              none
              =>
              get_local `this >> simp_at [ some `this , none ] assumption
                <|>
                simp_at [ none ] assumption
            |
              some e
              =>
              focus1
                do
                  let
                      e
                        ←
                        i_to_expr e
                          <|>
                          do
                            let ty ← target
                              let e ← i_to_expr_strict ` `( ( $ ( e ) : $ ( ty ) ) )
                              let pty ← pp ty
                              let ptgt ← pp e
                              fail
                                (
                                  "simpa failed, 'using' expression type not directly "
                                          ++
                                          "inferrable. Try:\n\nsimpa ... using\nshow "
                                        ++
                                        to_fmt pty
                                      ++
                                      ",\nfrom "
                                    ++
                                    ptgt
                                  :
                                  format
                                  )
                    match
                      e
                      with
                      |
                          local_const _ lc _ _
                          =>
                          simp_at [ some lc , none ] get_local lc >>= tactic.exact
                        |
                          e
                          =>
                          do
                            let t ← infer_type e
                              assertv `this t e
                              simp_at [ some `this , none ] get_local `this >>= tactic.exact
                              all_goals try apply_instance
#align tactic.interactive.simpa tactic.interactive.simpa

add_tactic_doc
  { Name := "simpa"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.simpa]
    tags := ["simplification"] }

end Interactive

end Tactic

