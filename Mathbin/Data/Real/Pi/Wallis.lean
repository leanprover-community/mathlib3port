import Mathbin.Analysis.SpecialFunctions.Integrals

/-! ### The Wallis Product for Pi -/


namespace Real

open_locale Real TopologicalSpace BigOperators

open Filter Finset intervalIntegral

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `integral_sin_pow_div_tendsto_one [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    (Term.app
     `tendsto
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`k] [])]
        "=>"
        («term_/_»
         (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
          "∫"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          " in "
          (numLit "0")
          ".."
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
          ", "
          (Cardinal.SetTheory.Cofinality.«term_^_»
           (Term.app `sin [`x])
           "^"
           (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `k) "+" (numLit "1"))))
         "/"
         (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
          "∫"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          " in "
          (numLit "0")
          ".."
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
          ", "
          (Cardinal.SetTheory.Cofinality.«term_^_»
           (Term.app `sin [`x])
           "^"
           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `k))))))
      `at_top
      (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "1")])])))
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
           [`h₃ []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n] [])]
              ","
              («term_≤_»
               («term_/_»
                (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                 "∫"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                 " in "
                 (numLit "0")
                 ".."
                 (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                 ", "
                 (Cardinal.SetTheory.Cofinality.«term_^_»
                  (Term.app `sin [`x])
                  "^"
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))
                "/"
                (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                 "∫"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                 " in "
                 (numLit "0")
                 ".."
                 (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                 ", "
                 (Cardinal.SetTheory.Cofinality.«term_^_»
                  (Term.app `sin [`x])
                  "^"
                  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n))))
               "≤"
               (numLit "1"))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`n] [])]
             "=>"
             (Term.app
              (Term.proj (Term.app `div_le_one [(Term.app `integral_sin_pow_pos [(Term.hole "_")])]) "." `mpr)
              [(Term.app `integral_sin_pow_succ_le [(Term.hole "_")])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h₄ []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n] [])]
              ","
              («term_≥_»
               («term_/_»
                (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                 "∫"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                 " in "
                 (numLit "0")
                 ".."
                 (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                 ", "
                 (Cardinal.SetTheory.Cofinality.«term_^_»
                  (Term.app `sin [`x])
                  "^"
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))
                "/"
                (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                 "∫"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                 " in "
                 (numLit "0")
                 ".."
                 (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                 ", "
                 (Cardinal.SetTheory.Cofinality.«term_^_»
                  (Term.app `sin [`x])
                  "^"
                  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n))))
               "≥"
               («term_/_»
                (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                "/"
                (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rintro
                 "rintro"
                 [(Tactic.rintroPat.one
                   (Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])]
                    "⟩"))]
                 [])
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.have''
                      "have"
                      []
                      [(Term.typeSpec
                        ":"
                        («term_≤_»
                         (numLit "0")
                         "≤"
                         («term_/_»
                          (Init.Logic.«term_+_» (numLit "1") "+" (numLit "1"))
                          "/"
                          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π"))))])
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `div_nonneg
                       [(Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                        `pi_pos.le]))
                     [])
                    (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])])))
                [])
               (group
                (tacticCalc_
                 "calc"
                 [(calcStep
                   («term_≥_»
                    («term_/_»
                     (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                      "∫"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                      " in "
                      (numLit "0")
                      ".."
                      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                      ", "
                      (Cardinal.SetTheory.Cofinality.«term_^_»
                       (Term.app `sin [`x])
                       "^"
                       (Init.Logic.«term_+_»
                        (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ)
                        "+"
                        (numLit "1"))))
                     "/"
                     (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                      "∫"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                      " in "
                      (numLit "0")
                      ".."
                      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                      ", "
                      (Cardinal.SetTheory.Cofinality.«term_^_»
                       (Term.app `sin [`x])
                       "^"
                       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ))))
                    "≥"
                    («term_/_»
                     (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                      "∫"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                      " in "
                      (numLit "0")
                      ".."
                      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                      ", "
                      (Cardinal.SetTheory.Cofinality.«term_^_»
                       (Term.app `sin [`x])
                       "^"
                       (Init.Logic.«term_+_»
                        (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ)
                        "+"
                        (numLit "1"))))
                     "/"
                     (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                      "∫"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                      " in "
                      (numLit "0")
                      ".."
                      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                      ", "
                      (Cardinal.SetTheory.Cofinality.«term_^_»
                       (Term.app `sin [`x])
                       "^"
                       (Init.Logic.«term_+_»
                        (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                        "+"
                        (numLit "1"))))))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.refine'
                         "refine'"
                         (Term.app
                          `div_le_div
                          [(Term.proj (Term.app `integral_sin_pow_pos [(Term.hole "_")]) "." `le)
                           (Term.app `le_reflₓ [(Term.hole "_")])
                           (Term.app `integral_sin_pow_pos [(Term.hole "_")])
                           (Term.hole "_")]))
                        [])
                       (group
                        (Tactic.convert
                         "convert"
                         []
                         (Term.app
                          `integral_sin_pow_succ_le
                          [(Init.Logic.«term_+_»
                            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                            "+"
                            (numLit "1"))])
                         ["using" (numLit "1")])
                        [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    («term_/_»
                     (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
                     "/"
                     (Init.Logic.«term_+_»
                      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
                      "+"
                      (numLit "1"))))
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
                            []
                            (Term.app
                             `div_eq_iff
                             [(Term.proj
                               (Term.app
                                `integral_sin_pow_pos
                                [(Init.Logic.«term_+_»
                                  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                                  "+"
                                  (numLit "1"))])
                               "."
                               `ne')]))]
                          "]")
                         [])
                        [])
                       (group
                        (Tactic.convert
                         "convert"
                         []
                         (Term.app
                          `integral_sin_pow
                          [(Init.Logic.«term_+_»
                            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                            "+"
                            (numLit "1"))])
                         [])
                        [])
                       (group (Tactic.simp' "simp'" [] [] [] [] ["with" [`field_simps]] []) [])
                       (group (Tactic.normCast "norm_cast" []) [])]))))])
                [])]))))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `tendsto_of_tendsto_of_tendsto_of_le_of_le
          [(Term.hole "_")
           (Term.hole "_")
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.proj (Term.app `h₄ [`n]) "." `le)))
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `h₃ [`n])))]))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.refine'
              "refine'"
              (Term.app
               `metric.tendsto_at_top.mpr
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`ε `hε] [])]
                  "=>"
                  (Term.anonymousCtor
                   "⟨"
                   [(Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊")
                    ","
                    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn] [])] "=>" (Term.hole "_")))]
                   "⟩")))]))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   («term_-_»
                    («term_/_»
                     (Finset.Data.Finset.Fold.«term_*_»
                      (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                      "*"
                      `n)
                     "/"
                     (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
                    "-"
                    (numLit "1"))
                   "="
                   («term_/_»
                    («term-_» "-" (numLit "1"))
                    "/"
                    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Mathlib.Tactic.Conv.convLHS
                      "conv_lhs"
                      []
                      []
                      "=>"
                      (Tactic.Conv.convSeq
                       (Tactic.Conv.convSeq1Indented
                        [(group (Tactic.Conv.congr "congr") [])
                         (group (Tactic.Conv.convSkip "skip") [])
                         (group
                          (Tactic.Conv.convRw__
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule
                              ["←"]
                              (Term.app
                               (Term.explicit "@" `div_self)
                               [(Term.hole "_")
                                (Term.hole "_")
                                (Init.Logic.«term_+_»
                                 (Finset.Data.Finset.Fold.«term_*_»
                                  (Term.paren
                                   "("
                                   [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]]
                                   ")")
                                  "*"
                                  `n)
                                 "+"
                                 (numLit "1"))
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group (Tactic.normCast "norm_cast" []) [])
                                    (group (Tactic.linarith "linarith" [] [] []) [])])))]))]
                            "]"))
                          [])])))
                     [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule ["←"] `sub_div)
                        ","
                        (Tactic.rwRule ["←"] `sub_sub)
                        ","
                        (Tactic.rwRule [] `sub_self)
                        ","
                        (Tactic.rwRule [] `zero_sub)]
                       "]")
                      [])
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hpos []]
                [(Term.typeSpec
                  ":"
                  («term_<_»
                   (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                   "<"
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.normCast "norm_cast" []) []) (group (Lean.Tactic.normNum "norm_num" [] []) [])]))))))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `dist_eq)
                ","
                (Tactic.rwRule [] `h)
                ","
                (Tactic.rwRule [] `abs_div)
                ","
                (Tactic.rwRule [] `abs_neg)
                ","
                (Tactic.rwRule [] `abs_one)
                ","
                (Tactic.rwRule [] (Term.app `abs_of_pos [`hpos]))
                ","
                (Tactic.rwRule [] (Term.app `one_div_lt [`hpos `hε]))]
               "]")
              [])
             [])
            (group
             (tacticCalc_
              "calc"
              [(calcStep
                («term_≤_»
                 («term_/_» (numLit "1") "/" `ε)
                 "≤"
                 (Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊"))
                ":="
                (Term.app `Nat.le_ceil [(Term.hole "_")]))
               (calcStep
                («term_≤_» (Term.hole "_") "≤" `n)
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `hn.le) [])]))))
               (calcStep
                («term_<_»
                 (Term.hole "_")
                 "<"
                 (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.normCast "norm_cast" []) []) (group (Tactic.linarith "linarith" [] [] []) [])]))))])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `tendsto_const_nhds) [])])))
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
          [`h₃ []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n] [])]
             ","
             («term_≤_»
              («term_/_»
               (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                "∫"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                " in "
                (numLit "0")
                ".."
                (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_»
                 (Term.app `sin [`x])
                 "^"
                 (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))
               "/"
               (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                "∫"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                " in "
                (numLit "0")
                ".."
                (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_»
                 (Term.app `sin [`x])
                 "^"
                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n))))
              "≤"
              (numLit "1"))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`n] [])]
            "=>"
            (Term.app
             (Term.proj (Term.app `div_le_one [(Term.app `integral_sin_pow_pos [(Term.hole "_")])]) "." `mpr)
             [(Term.app `integral_sin_pow_succ_le [(Term.hole "_")])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h₄ []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n] [])]
             ","
             («term_≥_»
              («term_/_»
               (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                "∫"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                " in "
                (numLit "0")
                ".."
                (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_»
                 (Term.app `sin [`x])
                 "^"
                 (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))
               "/"
               (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                "∫"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                " in "
                (numLit "0")
                ".."
                (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_»
                 (Term.app `sin [`x])
                 "^"
                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n))))
              "≥"
              («term_/_»
               (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
               "/"
               (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])]
                   "⟩"))]
                [])
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.have''
                     "have"
                     []
                     [(Term.typeSpec
                       ":"
                       («term_≤_»
                        (numLit "0")
                        "≤"
                        («term_/_»
                         (Init.Logic.«term_+_» (numLit "1") "+" (numLit "1"))
                         "/"
                         (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π"))))])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `div_nonneg
                      [(Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                       `pi_pos.le]))
                    [])
                   (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])])))
               [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_≥_»
                   («term_/_»
                    (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                     "∫"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                     " in "
                     (numLit "0")
                     ".."
                     (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                     ", "
                     (Cardinal.SetTheory.Cofinality.«term_^_»
                      (Term.app `sin [`x])
                      "^"
                      (Init.Logic.«term_+_»
                       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ)
                       "+"
                       (numLit "1"))))
                    "/"
                    (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                     "∫"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                     " in "
                     (numLit "0")
                     ".."
                     (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                     ", "
                     (Cardinal.SetTheory.Cofinality.«term_^_»
                      (Term.app `sin [`x])
                      "^"
                      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ))))
                   "≥"
                   («term_/_»
                    (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                     "∫"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                     " in "
                     (numLit "0")
                     ".."
                     (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                     ", "
                     (Cardinal.SetTheory.Cofinality.«term_^_»
                      (Term.app `sin [`x])
                      "^"
                      (Init.Logic.«term_+_»
                       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ)
                       "+"
                       (numLit "1"))))
                    "/"
                    (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                     "∫"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                     " in "
                     (numLit "0")
                     ".."
                     (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                     ", "
                     (Cardinal.SetTheory.Cofinality.«term_^_»
                      (Term.app `sin [`x])
                      "^"
                      (Init.Logic.«term_+_»
                       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                       "+"
                       (numLit "1"))))))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.refine'
                        "refine'"
                        (Term.app
                         `div_le_div
                         [(Term.proj (Term.app `integral_sin_pow_pos [(Term.hole "_")]) "." `le)
                          (Term.app `le_reflₓ [(Term.hole "_")])
                          (Term.app `integral_sin_pow_pos [(Term.hole "_")])
                          (Term.hole "_")]))
                       [])
                      (group
                       (Tactic.convert
                        "convert"
                        []
                        (Term.app
                         `integral_sin_pow_succ_le
                         [(Init.Logic.«term_+_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                           "+"
                           (numLit "1"))])
                        ["using" (numLit "1")])
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_/_»
                    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
                    "/"
                    (Init.Logic.«term_+_»
                     (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
                     "+"
                     (numLit "1"))))
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
                           []
                           (Term.app
                            `div_eq_iff
                            [(Term.proj
                              (Term.app
                               `integral_sin_pow_pos
                               [(Init.Logic.«term_+_»
                                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                                 "+"
                                 (numLit "1"))])
                              "."
                              `ne')]))]
                         "]")
                        [])
                       [])
                      (group
                       (Tactic.convert
                        "convert"
                        []
                        (Term.app
                         `integral_sin_pow
                         [(Init.Logic.«term_+_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                           "+"
                           (numLit "1"))])
                        [])
                       [])
                      (group (Tactic.simp' "simp'" [] [] [] [] ["with" [`field_simps]] []) [])
                      (group (Tactic.normCast "norm_cast" []) [])]))))])
               [])]))))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `tendsto_of_tendsto_of_tendsto_of_le_of_le
         [(Term.hole "_")
          (Term.hole "_")
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.proj (Term.app `h₄ [`n]) "." `le)))
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `h₃ [`n])))]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.app
              `metric.tendsto_at_top.mpr
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`ε `hε] [])]
                 "=>"
                 (Term.anonymousCtor
                  "⟨"
                  [(Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊")
                   ","
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn] [])] "=>" (Term.hole "_")))]
                  "⟩")))]))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  («term_-_»
                   («term_/_»
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                     "*"
                     `n)
                    "/"
                    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
                   "-"
                   (numLit "1"))
                  "="
                  («term_/_»
                   («term-_» "-" (numLit "1"))
                   "/"
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Mathlib.Tactic.Conv.convLHS
                     "conv_lhs"
                     []
                     []
                     "=>"
                     (Tactic.Conv.convSeq
                      (Tactic.Conv.convSeq1Indented
                       [(group (Tactic.Conv.congr "congr") [])
                        (group (Tactic.Conv.convSkip "skip") [])
                        (group
                         (Tactic.Conv.convRw__
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule
                             ["←"]
                             (Term.app
                              (Term.explicit "@" `div_self)
                              [(Term.hole "_")
                               (Term.hole "_")
                               (Init.Logic.«term_+_»
                                (Finset.Data.Finset.Fold.«term_*_»
                                 (Term.paren
                                  "("
                                  [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]]
                                  ")")
                                 "*"
                                 `n)
                                "+"
                                (numLit "1"))
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented
                                  [(group (Tactic.normCast "norm_cast" []) [])
                                   (group (Tactic.linarith "linarith" [] [] []) [])])))]))]
                           "]"))
                         [])])))
                    [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule ["←"] `sub_div)
                       ","
                       (Tactic.rwRule ["←"] `sub_sub)
                       ","
                       (Tactic.rwRule [] `sub_self)
                       ","
                       (Tactic.rwRule [] `zero_sub)]
                      "]")
                     [])
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hpos []]
               [(Term.typeSpec
                 ":"
                 («term_<_»
                  (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                  "<"
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.normCast "norm_cast" []) []) (group (Lean.Tactic.normNum "norm_num" [] []) [])]))))))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `dist_eq)
               ","
               (Tactic.rwRule [] `h)
               ","
               (Tactic.rwRule [] `abs_div)
               ","
               (Tactic.rwRule [] `abs_neg)
               ","
               (Tactic.rwRule [] `abs_one)
               ","
               (Tactic.rwRule [] (Term.app `abs_of_pos [`hpos]))
               ","
               (Tactic.rwRule [] (Term.app `one_div_lt [`hpos `hε]))]
              "]")
             [])
            [])
           (group
            (tacticCalc_
             "calc"
             [(calcStep
               («term_≤_»
                («term_/_» (numLit "1") "/" `ε)
                "≤"
                (Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊"))
               ":="
               (Term.app `Nat.le_ceil [(Term.hole "_")]))
              (calcStep
               («term_≤_» (Term.hole "_") "≤" `n)
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `hn.le) [])]))))
              (calcStep
               («term_<_»
                (Term.hole "_")
                "<"
                (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.normCast "norm_cast" []) []) (group (Tactic.linarith "linarith" [] [] []) [])]))))])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `tendsto_const_nhds) [])])))
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
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `tendsto_const_nhds) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `tendsto_const_nhds)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tendsto_const_nhds
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.refine'
        "refine'"
        (Term.app
         `metric.tendsto_at_top.mpr
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`ε `hε] [])]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊")
              ","
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn] [])] "=>" (Term.hole "_")))]
             "⟩")))]))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h []]
          [(Term.typeSpec
            ":"
            («term_=_»
             («term_-_»
              («term_/_»
               (Finset.Data.Finset.Fold.«term_*_»
                (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                "*"
                `n)
               "/"
               (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
              "-"
              (numLit "1"))
             "="
             («term_/_»
              («term-_» "-" (numLit "1"))
              "/"
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Mathlib.Tactic.Conv.convLHS
                "conv_lhs"
                []
                []
                "=>"
                (Tactic.Conv.convSeq
                 (Tactic.Conv.convSeq1Indented
                  [(group (Tactic.Conv.congr "congr") [])
                   (group (Tactic.Conv.convSkip "skip") [])
                   (group
                    (Tactic.Conv.convRw__
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        ["←"]
                        (Term.app
                         (Term.explicit "@" `div_self)
                         [(Term.hole "_")
                          (Term.hole "_")
                          (Init.Logic.«term_+_»
                           (Finset.Data.Finset.Fold.«term_*_»
                            (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                            "*"
                            `n)
                           "+"
                           (numLit "1"))
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group (Tactic.normCast "norm_cast" []) [])
                              (group (Tactic.linarith "linarith" [] [] []) [])])))]))]
                      "]"))
                    [])])))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `sub_div)
                  ","
                  (Tactic.rwRule ["←"] `sub_sub)
                  ","
                  (Tactic.rwRule [] `sub_self)
                  ","
                  (Tactic.rwRule [] `zero_sub)]
                 "]")
                [])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hpos []]
          [(Term.typeSpec
            ":"
            («term_<_»
             (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
             "<"
             (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.normCast "norm_cast" []) []) (group (Lean.Tactic.normNum "norm_num" [] []) [])]))))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `dist_eq)
          ","
          (Tactic.rwRule [] `h)
          ","
          (Tactic.rwRule [] `abs_div)
          ","
          (Tactic.rwRule [] `abs_neg)
          ","
          (Tactic.rwRule [] `abs_one)
          ","
          (Tactic.rwRule [] (Term.app `abs_of_pos [`hpos]))
          ","
          (Tactic.rwRule [] (Term.app `one_div_lt [`hpos `hε]))]
         "]")
        [])
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           («term_/_» (numLit "1") "/" `ε)
           "≤"
           (Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊"))
          ":="
          (Term.app `Nat.le_ceil [(Term.hole "_")]))
         (calcStep
          («term_≤_» (Term.hole "_") "≤" `n)
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `hn.le) [])]))))
         (calcStep
          («term_<_»
           (Term.hole "_")
           "<"
           (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.normCast "norm_cast" []) []) (group (Tactic.linarith "linarith" [] [] []) [])]))))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
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
      («term_/_» (numLit "1") "/" `ε)
      "≤"
      (Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊"))
     ":="
     (Term.app `Nat.le_ceil [(Term.hole "_")]))
    (calcStep
     («term_≤_» (Term.hole "_") "≤" `n)
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `hn.le) [])]))))
    (calcStep
     («term_<_»
      (Term.hole "_")
      "<"
      (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.normCast "norm_cast" []) []) (group (Tactic.linarith "linarith" [] [] []) [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.normCast "norm_cast" []) []) (group (Tactic.linarith "linarith" [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.linarith "linarith" [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.linarith', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.normCast "norm_cast" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.normCast', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_»
   (Term.hole "_")
   "<"
   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []]
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
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `hn.le) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exactModCast "exact_mod_cast" `hn.le)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exactModCast', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn.le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.hole "_") "≤" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `Nat.le_ceil [(Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.le_ceil
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   («term_/_» (numLit "1") "/" `ε)
   "≤"
   (Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Algebra.Order.Floor.«term⌈_⌉₊»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» (numLit "1") "/" `ε)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  («term_/_» (numLit "1") "/" `ε)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `dist_eq)
     ","
     (Tactic.rwRule [] `h)
     ","
     (Tactic.rwRule [] `abs_div)
     ","
     (Tactic.rwRule [] `abs_neg)
     ","
     (Tactic.rwRule [] `abs_one)
     ","
     (Tactic.rwRule [] (Term.app `abs_of_pos [`hpos]))
     ","
     (Tactic.rwRule [] (Term.app `one_div_lt [`hpos `hε]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `one_div_lt [`hpos `hε])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hpos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `one_div_lt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `abs_of_pos [`hpos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hpos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `abs_of_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `abs_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `abs_neg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `abs_div
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dist_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hpos []]
     [(Term.typeSpec
       ":"
       («term_<_»
        (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
        "<"
        (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.normCast "norm_cast" []) []) (group (Lean.Tactic.normNum "norm_num" [] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.normCast "norm_cast" []) []) (group (Lean.Tactic.normNum "norm_num" [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Lean.Tactic.normNum "norm_num" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Tactic.normNum', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.normCast "norm_cast" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.normCast', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_»
   (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
   "<"
   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`h []]
     [(Term.typeSpec
       ":"
       («term_=_»
        («term_-_»
         («term_/_»
          (Finset.Data.Finset.Fold.«term_*_»
           (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
           "*"
           `n)
          "/"
          (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
         "-"
         (numLit "1"))
        "="
        («term_/_»
         («term-_» "-" (numLit "1"))
         "/"
         (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Mathlib.Tactic.Conv.convLHS
           "conv_lhs"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(group (Tactic.Conv.congr "congr") [])
              (group (Tactic.Conv.convSkip "skip") [])
              (group
               (Tactic.Conv.convRw__
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   ["←"]
                   (Term.app
                    (Term.explicit "@" `div_self)
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Init.Logic.«term_+_»
                      (Finset.Data.Finset.Fold.«term_*_»
                       (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                       "*"
                       `n)
                      "+"
                      (numLit "1"))
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.normCast "norm_cast" []) [])
                         (group (Tactic.linarith "linarith" [] [] []) [])])))]))]
                 "]"))
               [])])))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `sub_div)
             ","
             (Tactic.rwRule ["←"] `sub_sub)
             ","
             (Tactic.rwRule [] `sub_self)
             ","
             (Tactic.rwRule [] `zero_sub)]
            "]")
           [])
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
       (Mathlib.Tactic.Conv.convLHS
        "conv_lhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.congr "congr") [])
           (group (Tactic.Conv.convSkip "skip") [])
           (group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                ["←"]
                (Term.app
                 (Term.explicit "@" `div_self)
                 [(Term.hole "_")
                  (Term.hole "_")
                  (Init.Logic.«term_+_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                    "*"
                    `n)
                   "+"
                   (numLit "1"))
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.normCast "norm_cast" []) [])
                      (group (Tactic.linarith "linarith" [] [] []) [])])))]))]
              "]"))
            [])])))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `sub_div)
          ","
          (Tactic.rwRule ["←"] `sub_sub)
          ","
          (Tactic.rwRule [] `sub_self)
          ","
          (Tactic.rwRule [] `zero_sub)]
         "]")
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
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] `sub_div)
     ","
     (Tactic.rwRule ["←"] `sub_sub)
     ","
     (Tactic.rwRule [] `sub_self)
     ","
     (Tactic.rwRule [] `zero_sub)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_sub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_self
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_sub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_div
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Conv.convLHS
   "conv_lhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group (Tactic.Conv.congr "congr") [])
      (group (Tactic.Conv.convSkip "skip") [])
      (group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           ["←"]
           (Term.app
            (Term.explicit "@" `div_self)
            [(Term.hole "_")
             (Term.hole "_")
             (Init.Logic.«term_+_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
               "*"
               `n)
              "+"
              (numLit "1"))
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.normCast "norm_cast" []) []) (group (Tactic.linarith "linarith" [] [] []) [])])))]))]
         "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.explicit "@" `div_self)
   [(Term.hole "_")
    (Term.hole "_")
    (Init.Logic.«term_+_»
     (Finset.Data.Finset.Fold.«term_*_»
      (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
      "*"
      `n)
     "+"
     (numLit "1"))
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.normCast "norm_cast" []) []) (group (Tactic.linarith "linarith" [] [] []) [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.normCast "norm_cast" []) []) (group (Tactic.linarith "linarith" [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.linarith "linarith" [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.linarith', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.normCast "norm_cast" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.normCast', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.normCast "norm_cast" []) []) (group (Tactic.linarith "linarith" [] [] []) [])])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
    "*"
    `n)
   "+"
   (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
   "*"
   `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
   "*"
   `n)
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_»
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_»
      (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
      "*"
      `n)
     []]
    ")")
   "+"
   (numLit "1"))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
  (Term.explicit "@" `div_self)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `div_self
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSkip', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.congr', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   («term_-_»
    («term_/_»
     (Finset.Data.Finset.Fold.«term_*_»
      (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
      "*"
      `n)
     "/"
     (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
    "-"
    (numLit "1"))
   "="
   («term_/_»
    («term-_» "-" (numLit "1"))
    "/"
    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   («term-_» "-" (numLit "1"))
   "/"
   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  («term-_» "-" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 100, (some 100, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  («term_-_»
   («term_/_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
     "*"
     `n)
    "/"
    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
   "-"
   (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  («term_/_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
    "*"
    `n)
   "/"
   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
   "*"
   `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
   "*"
   `n)
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_/_»
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_»
      (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
      "*"
      `n)
     []]
    ")")
   "/"
   (Init.Logic.«term_+_»
    (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []] ")")
    "+"
    (numLit "1")))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `metric.tendsto_at_top.mpr
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`ε `hε] [])]
       "=>"
       (Term.anonymousCtor
        "⟨"
        [(Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊")
         ","
         (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn] [])] "=>" (Term.hole "_")))]
        "⟩")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `metric.tendsto_at_top.mpr
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`ε `hε] [])]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [(Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊")
        ","
        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn] [])] "=>" (Term.hole "_")))]
       "⟩")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`ε `hε] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [(Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊")
      ","
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn] [])] "=>" (Term.hole "_")))]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊")
    ","
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn] [])] "=>" (Term.hole "_")))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Algebra.Order.Floor.«term⌈_⌉₊»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Algebra.Order.Floor.«term⌈_⌉₊» "⌈" («term_/_» (numLit "1") "/" `ε) "⌉₊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Algebra.Order.Floor.«term⌈_⌉₊»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» (numLit "1") "/" `ε)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `metric.tendsto_at_top.mpr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `tendsto_of_tendsto_of_tendsto_of_le_of_le
    [(Term.hole "_")
     (Term.hole "_")
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.proj (Term.app `h₄ [`n]) "." `le)))
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `h₃ [`n])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `tendsto_of_tendsto_of_tendsto_of_le_of_le
   [(Term.hole "_")
    (Term.hole "_")
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.proj (Term.app `h₄ [`n]) "." `le)))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `h₃ [`n])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `h₃ [`n])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h₃ [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h₃
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.proj (Term.app `h₄ [`n]) "." `le)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `h₄ [`n]) "." `le)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `h₄ [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h₄
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `h₄ [`n]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.proj (Term.paren "(" [(Term.app `h₄ [`n]) []] ")") "." `le)))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
  `tendsto_of_tendsto_of_tendsto_of_le_of_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`h₄ []]
     [(Term.typeSpec
       ":"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`n] [])]
        ","
        («term_≥_»
         («term_/_»
          (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
           "∫"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           " in "
           (numLit "0")
           ".."
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
           ", "
           (Cardinal.SetTheory.Cofinality.«term_^_»
            (Term.app `sin [`x])
            "^"
            (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))
          "/"
          (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
           "∫"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           " in "
           (numLit "0")
           ".."
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
           ", "
           (Cardinal.SetTheory.Cofinality.«term_^_»
            (Term.app `sin [`x])
            "^"
            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n))))
         "≥"
         («term_/_»
          (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
          "/"
          (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rintro
           "rintro"
           [(Tactic.rintroPat.one
             (Tactic.rcasesPat.tuple
              "⟨"
              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])]
              "⟩"))]
           [])
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.have''
                "have"
                []
                [(Term.typeSpec
                  ":"
                  («term_≤_»
                   (numLit "0")
                   "≤"
                   («term_/_»
                    (Init.Logic.«term_+_» (numLit "1") "+" (numLit "1"))
                    "/"
                    (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π"))))])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `div_nonneg
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                  `pi_pos.le]))
               [])
              (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])])))
          [])
         (group
          (tacticCalc_
           "calc"
           [(calcStep
             («term_≥_»
              («term_/_»
               (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                "∫"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                " in "
                (numLit "0")
                ".."
                (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_»
                 (Term.app `sin [`x])
                 "^"
                 (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ) "+" (numLit "1"))))
               "/"
               (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                "∫"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                " in "
                (numLit "0")
                ".."
                (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_»
                 (Term.app `sin [`x])
                 "^"
                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ))))
              "≥"
              («term_/_»
               (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                "∫"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                " in "
                (numLit "0")
                ".."
                (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_»
                 (Term.app `sin [`x])
                 "^"
                 (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ) "+" (numLit "1"))))
               "/"
               (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
                "∫"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
                " in "
                (numLit "0")
                ".."
                (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                ", "
                (Cardinal.SetTheory.Cofinality.«term_^_»
                 (Term.app `sin [`x])
                 "^"
                 (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `div_le_div
                    [(Term.proj (Term.app `integral_sin_pow_pos [(Term.hole "_")]) "." `le)
                     (Term.app `le_reflₓ [(Term.hole "_")])
                     (Term.app `integral_sin_pow_pos [(Term.hole "_")])
                     (Term.hole "_")]))
                  [])
                 (group
                  (Tactic.convert
                   "convert"
                   []
                   (Term.app
                    `integral_sin_pow_succ_le
                    [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
                   ["using" (numLit "1")])
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_/_»
               (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
               "/"
               (Init.Logic.«term_+_»
                (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
                "+"
                (numLit "1"))))
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
                      []
                      (Term.app
                       `div_eq_iff
                       [(Term.proj
                         (Term.app
                          `integral_sin_pow_pos
                          [(Init.Logic.«term_+_»
                            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                            "+"
                            (numLit "1"))])
                         "."
                         `ne')]))]
                    "]")
                   [])
                  [])
                 (group
                  (Tactic.convert
                   "convert"
                   []
                   (Term.app
                    `integral_sin_pow
                    [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
                   [])
                  [])
                 (group (Tactic.simp' "simp'" [] [] [] [] ["with" [`field_simps]] []) [])
                 (group (Tactic.normCast "norm_cast" []) [])]))))])
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
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])] "⟩"))]
        [])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.have''
             "have"
             []
             [(Term.typeSpec
               ":"
               («term_≤_»
                (numLit "0")
                "≤"
                («term_/_»
                 (Init.Logic.«term_+_» (numLit "1") "+" (numLit "1"))
                 "/"
                 (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π"))))])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              `div_nonneg
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
               `pi_pos.le]))
            [])
           (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])])))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≥_»
           («term_/_»
            (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
             "∫"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             (numLit "0")
             ".."
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app `sin [`x])
              "^"
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ) "+" (numLit "1"))))
            "/"
            (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
             "∫"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             (numLit "0")
             ".."
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app `sin [`x])
              "^"
              (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ))))
           "≥"
           («term_/_»
            (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
             "∫"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             (numLit "0")
             ".."
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app `sin [`x])
              "^"
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ) "+" (numLit "1"))))
            "/"
            (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
             "∫"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             (numLit "0")
             ".."
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
             ", "
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.app `sin [`x])
              "^"
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `div_le_div
                 [(Term.proj (Term.app `integral_sin_pow_pos [(Term.hole "_")]) "." `le)
                  (Term.app `le_reflₓ [(Term.hole "_")])
                  (Term.app `integral_sin_pow_pos [(Term.hole "_")])
                  (Term.hole "_")]))
               [])
              (group
               (Tactic.convert
                "convert"
                []
                (Term.app
                 `integral_sin_pow_succ_le
                 [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
                ["using" (numLit "1")])
               [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           («term_/_»
            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
            "/"
            (Init.Logic.«term_+_»
             (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
             "+"
             (numLit "1"))))
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
                   []
                   (Term.app
                    `div_eq_iff
                    [(Term.proj
                      (Term.app
                       `integral_sin_pow_pos
                       [(Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                         "+"
                         (numLit "1"))])
                      "."
                      `ne')]))]
                 "]")
                [])
               [])
              (group
               (Tactic.convert
                "convert"
                []
                (Term.app
                 `integral_sin_pow
                 [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
                [])
               [])
              (group (Tactic.simp' "simp'" [] [] [] [] ["with" [`field_simps]] []) [])
              (group (Tactic.normCast "norm_cast" []) [])]))))])
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
     («term_≥_»
      («term_/_»
       (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
        "∫"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
        " in "
        (numLit "0")
        ".."
        (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
        ", "
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Term.app `sin [`x])
         "^"
         (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ) "+" (numLit "1"))))
       "/"
       (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
        "∫"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
        " in "
        (numLit "0")
        ".."
        (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
        ", "
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Term.app `sin [`x])
         "^"
         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ))))
      "≥"
      («term_/_»
       (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
        "∫"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
        " in "
        (numLit "0")
        ".."
        (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
        ", "
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Term.app `sin [`x])
         "^"
         (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ) "+" (numLit "1"))))
       "/"
       (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
        "∫"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
        " in "
        (numLit "0")
        ".."
        (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
        ", "
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Term.app `sin [`x])
         "^"
         (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.refine'
           "refine'"
           (Term.app
            `div_le_div
            [(Term.proj (Term.app `integral_sin_pow_pos [(Term.hole "_")]) "." `le)
             (Term.app `le_reflₓ [(Term.hole "_")])
             (Term.app `integral_sin_pow_pos [(Term.hole "_")])
             (Term.hole "_")]))
          [])
         (group
          (Tactic.convert
           "convert"
           []
           (Term.app
            `integral_sin_pow_succ_le
            [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
           ["using" (numLit "1")])
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      («term_/_»
       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
       "/"
       (Init.Logic.«term_+_»
        (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
        "+"
        (numLit "1"))))
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
              []
              (Term.app
               `div_eq_iff
               [(Term.proj
                 (Term.app
                  `integral_sin_pow_pos
                  [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
                 "."
                 `ne')]))]
            "]")
           [])
          [])
         (group
          (Tactic.convert
           "convert"
           []
           (Term.app
            `integral_sin_pow
            [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
           [])
          [])
         (group (Tactic.simp' "simp'" [] [] [] [] ["with" [`field_simps]] []) [])
         (group (Tactic.normCast "norm_cast" []) [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
           []
           (Term.app
            `div_eq_iff
            [(Term.proj
              (Term.app
               `integral_sin_pow_pos
               [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
              "."
              `ne')]))]
         "]")
        [])
       [])
      (group
       (Tactic.convert
        "convert"
        []
        (Term.app
         `integral_sin_pow
         [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
        [])
       [])
      (group (Tactic.simp' "simp'" [] [] [] [] ["with" [`field_simps]] []) [])
      (group (Tactic.normCast "norm_cast" []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.normCast "norm_cast" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.normCast', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp' "simp'" [] [] [] [] ["with" [`field_simps]] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.convert
   "convert"
   []
   (Term.app
    `integral_sin_pow
    [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `integral_sin_pow
   [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_»
   (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []] ")")
   "+"
   (numLit "1"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `integral_sin_pow
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.app
       `div_eq_iff
       [(Term.proj
         (Term.app
          `integral_sin_pow_pos
          [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
         "."
         `ne')]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `div_eq_iff
   [(Term.proj
     (Term.app
      `integral_sin_pow_pos
      [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
     "."
     `ne')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    `integral_sin_pow_pos
    [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
   "."
   `ne')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `integral_sin_pow_pos
   [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_»
   (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []] ")")
   "+"
   (numLit "1"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `integral_sin_pow_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `integral_sin_pow_pos
   [(Term.paren
     "("
     [(Init.Logic.«term_+_»
       (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []] ")")
       "+"
       (numLit "1"))
      []]
     ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `div_eq_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   («term_/_»
    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
    "/"
    (Init.Logic.«term_+_»
     (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
     "+"
     (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
   "/"
   (Init.Logic.«term_+_»
    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
    "+"
    (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_»
   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
   "+"
   (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↑_» "↑" `n.succ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n.succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↑_» "↑" `n.succ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n.succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `n.succ)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 0, term) <=? (none, [anonymous])
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
       (Tactic.refine'
        "refine'"
        (Term.app
         `div_le_div
         [(Term.proj (Term.app `integral_sin_pow_pos [(Term.hole "_")]) "." `le)
          (Term.app `le_reflₓ [(Term.hole "_")])
          (Term.app `integral_sin_pow_pos [(Term.hole "_")])
          (Term.hole "_")]))
       [])
      (group
       (Tactic.convert
        "convert"
        []
        (Term.app
         `integral_sin_pow_succ_le
         [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
        ["using" (numLit "1")])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.convert
   "convert"
   []
   (Term.app
    `integral_sin_pow_succ_le
    [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
   ["using" (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `integral_sin_pow_succ_le
   [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_»
   (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []] ")")
   "+"
   (numLit "1"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `integral_sin_pow_succ_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `div_le_div
    [(Term.proj (Term.app `integral_sin_pow_pos [(Term.hole "_")]) "." `le)
     (Term.app `le_reflₓ [(Term.hole "_")])
     (Term.app `integral_sin_pow_pos [(Term.hole "_")])
     (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `div_le_div
   [(Term.proj (Term.app `integral_sin_pow_pos [(Term.hole "_")]) "." `le)
    (Term.app `le_reflₓ [(Term.hole "_")])
    (Term.app `integral_sin_pow_pos [(Term.hole "_")])
    (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `integral_sin_pow_pos [(Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `integral_sin_pow_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `integral_sin_pow_pos [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `le_reflₓ [(Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_reflₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_reflₓ [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `integral_sin_pow_pos [(Term.hole "_")]) "." `le)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `integral_sin_pow_pos [(Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `integral_sin_pow_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `integral_sin_pow_pos [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `div_le_div
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≥_»
   («term_/_»
    (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
     "∫"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
     " in "
     (numLit "0")
     ".."
     (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
     ", "
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.app `sin [`x])
      "^"
      (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ) "+" (numLit "1"))))
    "/"
    (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
     "∫"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
     " in "
     (numLit "0")
     ".."
     (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
     ", "
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.app `sin [`x])
      "^"
      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ))))
   "≥"
   («term_/_»
    (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
     "∫"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
     " in "
     (numLit "0")
     ".."
     (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
     ", "
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.app `sin [`x])
      "^"
      (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ) "+" (numLit "1"))))
    "/"
    (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
     "∫"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
     " in "
     (numLit "0")
     ".."
     (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
     ", "
     (Cardinal.SetTheory.Cofinality.«term_^_»
      (Term.app `sin [`x])
      "^"
      (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≥_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
    "∫"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
    " in "
    (numLit "0")
    ".."
    (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
    ", "
    (Cardinal.SetTheory.Cofinality.«term_^_»
     (Term.app `sin [`x])
     "^"
     (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n.succ) "+" (numLit "1"))))
   "/"
   (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
    "∫"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
    " in "
    (numLit "0")
    ".."
    (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
    ", "
    (Cardinal.SetTheory.Cofinality.«term_^_»
     (Term.app `sin [`x])
     "^"
     (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»
   "∫"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
   " in "
   (numLit "0")
   ".."
   (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
   ", "
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.app `sin [`x])
    "^"
    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.Integral.IntervalIntegral.«term∫_in_.._,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.app `sin [`x])
   "^"
   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.app `sin [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sin
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1022, (some 1023, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
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
theorem
  integral_sin_pow_div_tendsto_one
  : tendsto fun k => ∫ x in 0 .. π , sin x ^ 2 * k + 1 / ∫ x in 0 .. π , sin x ^ 2 * k at_top 𝓝 1
  :=
    by
      have
          h₃
            : ∀ n , ∫ x in 0 .. π , sin x ^ 2 * n + 1 / ∫ x in 0 .. π , sin x ^ 2 * n ≤ 1
            :=
            fun n => div_le_one integral_sin_pow_pos _ . mpr integral_sin_pow_succ_le _
        have
          h₄
            : ∀ n , ∫ x in 0 .. π , sin x ^ 2 * n + 1 / ∫ x in 0 .. π , sin x ^ 2 * n ≥ 2 * n / 2 * n + 1
            :=
            by
              rintro ⟨ n ⟩
                · have : 0 ≤ 1 + 1 / π exact div_nonneg by norm_num pi_pos.le simp [ this ]
                calc
                  ∫ x in 0 .. π , sin x ^ 2 * n.succ + 1 / ∫ x in 0 .. π , sin x ^ 2 * n.succ
                        ≥
                        ∫ x in 0 .. π , sin x ^ 2 * n.succ + 1 / ∫ x in 0 .. π , sin x ^ 2 * n + 1
                      :=
                      by
                        refine' div_le_div integral_sin_pow_pos _ . le le_reflₓ _ integral_sin_pow_pos _ _
                          convert integral_sin_pow_succ_le 2 * n + 1 using 1
                    _ = 2 * ↑ n.succ / 2 * ↑ n.succ + 1
                      :=
                      by
                        rw [ div_eq_iff integral_sin_pow_pos 2 * n + 1 . ne' ]
                          convert integral_sin_pow 2 * n + 1
                          simp' with field_simps
                          norm_cast
        refine' tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ fun n => h₄ n . le fun n => h₃ n
        ·
          refine' metric.tendsto_at_top.mpr fun ε hε => ⟨ ⌈ 1 / ε ⌉₊ , fun n hn => _ ⟩
            have
              h
                : ( 2 : ℝ ) * n / 2 * n + 1 - 1 = - 1 / 2 * n + 1
                :=
                by
                  conv_lhs => congr skip rw [ ← @ div_self _ _ ( 2 : ℝ ) * n + 1 by norm_cast linarith ]
                    rw [ ← sub_div , ← sub_sub , sub_self , zero_sub ]
            have hpos : ( 0 : ℝ ) < 2 * n + 1 := by norm_cast norm_num
            rw [ dist_eq , h , abs_div , abs_neg , abs_one , abs_of_pos hpos , one_div_lt hpos hε ]
            calc
              1 / ε ≤ ⌈ 1 / ε ⌉₊ := Nat.le_ceil _
                _ ≤ n := by exact_mod_cast hn.le
                _ < 2 * n + 1 := by norm_cast linarith
        · exact tendsto_const_nhds

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " This theorem establishes the Wallis Product for `π`. Our proof is largely about analyzing\n  the behavior of the ratio of the integral of `sin x ^ n` as `n → ∞`.\n  See: https://en.wikipedia.org/wiki/Wallis_product\n\n  The proof can be broken down into two pieces.\n  (Pieces involving general properties of the integral of `sin x ^n` can be found\n  in `analysis.special_functions.integrals`.) First, we use integration by parts to obtain a\n  recursive formula for `∫ x in 0..π, sin x ^ (n + 2)` in terms of `∫ x in 0..π, sin x ^ n`.\n  From this we can obtain closed form products of `∫ x in 0..π, sin x ^ (2 * n)` and\n  `∫ x in 0..π, sin x ^ (2 * n + 1)` via induction. Next, we study the behavior of the ratio\n  `∫ (x : ℝ) in 0..π, sin x ^ (2 * k + 1)) / ∫ (x : ℝ) in 0..π, sin x ^ (2 * k)` and prove that\n  it converges to one using the squeeze theorem. The final product for `π` is obtained after some\n  algebraic manipulation. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `tendsto_prod_pi_div_two [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    (Term.app
     `tendsto
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`k] [])]
        "=>"
        (Algebra.BigOperators.Basic.«term∏_in_,_»
         "∏"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         " in "
         (Term.app `range [`k])
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          («term_/_»
           (Init.Logic.«term_+_»
            (Finset.Data.Finset.Fold.«term_*_»
             (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
             "*"
             `i)
            "+"
            (numLit "2"))
           "/"
           (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "1")))
          "*"
          («term_/_»
           (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
           "/"
           (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "3")))))))
      `at_top
      (Term.app
       (Topology.Basic.term𝓝 "𝓝")
       [(«term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π") "/" (numLit "2"))])])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.suffices'
         "suffices"
         [`h []]
         [(Term.typeSpec
           ":"
           (Term.app
            `tendsto
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`k] [])]
               "=>"
               (Finset.Data.Finset.Fold.«term_*_»
                («term_/_» (numLit "2") "/" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π"))
                "*"
                (Algebra.BigOperators.Basic.«term∏_in_,_»
                 "∏"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                 " in "
                 (Term.app `range [`k])
                 ", "
                 (Finset.Data.Finset.Fold.«term_*_»
                  («term_/_»
                   (Init.Logic.«term_+_»
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                     "*"
                     `i)
                    "+"
                    (numLit "2"))
                   "/"
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "1")))
                  "*"
                  («term_/_»
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
                   "/"
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "3"))))))))
             `at_top
             (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "1")])]))])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                []
                ":="
                (Term.app
                 `tendsto.const_mul
                 [(«term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π") "/" (numLit "2")) `h]))))
             [])
            (group
             (Tactic.have''
              "have"
              [`h []]
              [(Term.typeSpec
                ":"
                («term_≠_»
                 («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π") "/" (numLit "2"))
                 "≠"
                 (numLit "0")))])
             [])
            (group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `pi_ne_zero)] "]"] []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] ["←"] `mul_assocₓ)
                ","
                (Tactic.simpLemma
                 []
                 ["←"]
                 (Term.app
                  (Term.explicit "@" `inv_div)
                  [(Term.hole "_")
                   (Term.hole "_")
                   (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                   (numLit "2")]))
                ","
                (Tactic.simpLemma [] [] (Term.app `mul_inv_cancel [`h]))
                ","
                (Tactic.simpLemma [] [] `one_mulₓ)
                ","
                (Tactic.simpLemma [] [] `mul_oneₓ)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
             [])
            (group (Tactic.exact "exact" `this) [])])))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                "=>"
                (Finset.Data.Finset.Fold.«term_*_»
                 («term_/_»
                  (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                  "/"
                  (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π"))
                 "*"
                 (Algebra.BigOperators.Basic.«term∏_in_,_»
                  "∏"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
                  " in "
                  (Term.app `range [`k])
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_»
                   («term_/_»
                    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
                    "/"
                    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "1")))
                   "*"
                   («term_/_»
                    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
                    "/"
                    (Init.Logic.«term_+_»
                     (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i)
                     "+"
                     (numLit "3"))))))))
              "="
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`k] [])]
                "=>"
                («term_/_»
                 (Finset.Data.Finset.Fold.«term_*_»
                  (numLit "2")
                  "*"
                  (Algebra.BigOperators.Basic.«term∏_in_,_»
                   "∏"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                   " in "
                   (Term.app `range [`k])
                   ", "
                   («term_/_»
                    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
                    "/"
                    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "3")))))
                 "/"
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                  "*"
                  (Algebra.BigOperators.Basic.«term∏_in_,_»
                   "∏"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
                   " in "
                   (Term.app `range [`k])
                   ", "
                   («term_/_»
                    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "1"))
                    "/"
                    (Init.Logic.«term_+_»
                     (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i)
                     "+"
                     (numLit "2"))))))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (tacticFunext__ "funext" []) [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`h []]
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (Algebra.BigOperators.Basic.«term∏_in_,_»
                       "∏"
                       (Lean.explicitBinders
                        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
                       " in "
                       (Term.app `range [`k])
                       ", "
                       («term_/_»
                        (Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                          "*"
                          (Init.Coe.«term↑_» "↑" `i))
                         "+"
                         (numLit "2"))
                        "/"
                        (Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                         "+"
                         (numLit "1"))))
                      "="
                      («term_/_»
                       (numLit "1")
                       "/"
                       (Algebra.BigOperators.Basic.«term∏_in_,_»
                        "∏"
                        (Lean.explicitBinders
                         (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
                        " in "
                        (Term.app `range [`k])
                        ", "
                        («term_/_»
                         (Init.Logic.«term_+_»
                          (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                          "+"
                          (numLit "1"))
                         "/"
                         (Init.Logic.«term_+_»
                          (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                          "+"
                          (numLit "2")))))))]
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
                          [(Tactic.rwRule [] `one_div) "," (Tactic.rwRule ["←"] `Finset.prod_inv_distrib')]
                          "]")
                         [])
                        [])
                       (group
                        (Tactic.refine'
                         "refine'"
                         (Term.app
                          `prod_congr
                          [`rfl
                           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
                        [])
                       (group (Tactic.fieldSimp "field_simp" [] [] [] [] []) [])]))))))
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `prod_mul_distrib) "," (Tactic.rwRule [] `h)] "]")
                 [])
                [])
               (group (Tactic.fieldSimp "field_simp" [] [] [] [] []) [])]))))))
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `h)
           ","
           (Tactic.simpLemma [] ["←"] `integral_sin_pow_even)
           ","
           (Tactic.simpLemma [] ["←"] `integral_sin_pow_odd)]
          "]"]
         [])
        [])
       (group (Tactic.exact "exact" `integral_sin_pow_div_tendsto_one) [])])))
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
       (Tactic.suffices'
        "suffices"
        [`h []]
        [(Term.typeSpec
          ":"
          (Term.app
           `tendsto
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`k] [])]
              "=>"
              (Finset.Data.Finset.Fold.«term_*_»
               («term_/_» (numLit "2") "/" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π"))
               "*"
               (Algebra.BigOperators.Basic.«term∏_in_,_»
                "∏"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                " in "
                (Term.app `range [`k])
                ", "
                (Finset.Data.Finset.Fold.«term_*_»
                 («term_/_»
                  (Init.Logic.«term_+_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                    "*"
                    `i)
                   "+"
                   (numLit "2"))
                  "/"
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "1")))
                 "*"
                 («term_/_»
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
                  "/"
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "3"))))))))
            `at_top
            (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "1")])]))])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               []
               ":="
               (Term.app
                `tendsto.const_mul
                [(«term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π") "/" (numLit "2")) `h]))))
            [])
           (group
            (Tactic.have''
             "have"
             [`h []]
             [(Term.typeSpec
               ":"
               («term_≠_»
                («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π") "/" (numLit "2"))
                "≠"
                (numLit "0")))])
            [])
           (group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `pi_ne_zero)] "]"] []) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] ["←"] `mul_assocₓ)
               ","
               (Tactic.simpLemma
                []
                ["←"]
                (Term.app
                 (Term.explicit "@" `inv_div)
                 [(Term.hole "_")
                  (Term.hole "_")
                  (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                  (numLit "2")]))
               ","
               (Tactic.simpLemma [] [] (Term.app `mul_inv_cancel [`h]))
               ","
               (Tactic.simpLemma [] [] `one_mulₓ)
               ","
               (Tactic.simpLemma [] [] `mul_oneₓ)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
            [])
           (group (Tactic.exact "exact" `this) [])])))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
               "=>"
               (Finset.Data.Finset.Fold.«term_*_»
                («term_/_»
                 (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                 "/"
                 (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π"))
                "*"
                (Algebra.BigOperators.Basic.«term∏_in_,_»
                 "∏"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
                 " in "
                 (Term.app `range [`k])
                 ", "
                 (Finset.Data.Finset.Fold.«term_*_»
                  («term_/_»
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
                   "/"
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "1")))
                  "*"
                  («term_/_»
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
                   "/"
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "3"))))))))
             "="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`k] [])]
               "=>"
               («term_/_»
                (Finset.Data.Finset.Fold.«term_*_»
                 (numLit "2")
                 "*"
                 (Algebra.BigOperators.Basic.«term∏_in_,_»
                  "∏"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                  " in "
                  (Term.app `range [`k])
                  ", "
                  («term_/_»
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
                   "/"
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "3")))))
                "/"
                (Finset.Data.Finset.Fold.«term_*_»
                 (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
                 "*"
                 (Algebra.BigOperators.Basic.«term∏_in_,_»
                  "∏"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
                  " in "
                  (Term.app `range [`k])
                  ", "
                  («term_/_»
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "1"))
                   "/"
                   (Init.Logic.«term_+_»
                    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i)
                    "+"
                    (numLit "2"))))))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (tacticFunext__ "funext" []) [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h []]
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Algebra.BigOperators.Basic.«term∏_in_,_»
                      "∏"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
                      " in "
                      (Term.app `range [`k])
                      ", "
                      («term_/_»
                       (Init.Logic.«term_+_»
                        (Finset.Data.Finset.Fold.«term_*_»
                         (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                         "*"
                         (Init.Coe.«term↑_» "↑" `i))
                        "+"
                        (numLit "2"))
                       "/"
                       (Init.Logic.«term_+_»
                        (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                        "+"
                        (numLit "1"))))
                     "="
                     («term_/_»
                      (numLit "1")
                      "/"
                      (Algebra.BigOperators.Basic.«term∏_in_,_»
                       "∏"
                       (Lean.explicitBinders
                        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
                       " in "
                       (Term.app `range [`k])
                       ", "
                       («term_/_»
                        (Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                         "+"
                         (numLit "1"))
                        "/"
                        (Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                         "+"
                         (numLit "2")))))))]
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
                         [(Tactic.rwRule [] `one_div) "," (Tactic.rwRule ["←"] `Finset.prod_inv_distrib')]
                         "]")
                        [])
                       [])
                      (group
                       (Tactic.refine'
                        "refine'"
                        (Term.app
                         `prod_congr
                         [`rfl
                          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
                       [])
                      (group (Tactic.fieldSimp "field_simp" [] [] [] [] []) [])]))))))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `prod_mul_distrib) "," (Tactic.rwRule [] `h)] "]")
                [])
               [])
              (group (Tactic.fieldSimp "field_simp" [] [] [] [] []) [])]))))))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `h)
          ","
          (Tactic.simpLemma [] ["←"] `integral_sin_pow_even)
          ","
          (Tactic.simpLemma [] ["←"] `integral_sin_pow_odd)]
         "]"]
        [])
       [])
      (group (Tactic.exact "exact" `integral_sin_pow_div_tendsto_one) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `integral_sin_pow_div_tendsto_one)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `integral_sin_pow_div_tendsto_one
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
    [(Tactic.simpLemma [] [] `h)
     ","
     (Tactic.simpLemma [] ["←"] `integral_sin_pow_even)
     ","
     (Tactic.simpLemma [] ["←"] `integral_sin_pow_odd)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `integral_sin_pow_odd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `integral_sin_pow_even
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`h []]
     [(Term.typeSpec
       ":"
       («term_=_»
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
          "=>"
          (Finset.Data.Finset.Fold.«term_*_»
           («term_/_»
            (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
            "/"
            (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π"))
           "*"
           (Algebra.BigOperators.Basic.«term∏_in_,_»
            "∏"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
            " in "
            (Term.app `range [`k])
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             («term_/_»
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
              "/"
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "1")))
             "*"
             («term_/_»
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
              "/"
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "3"))))))))
        "="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`k] [])]
          "=>"
          («term_/_»
           (Finset.Data.Finset.Fold.«term_*_»
            (numLit "2")
            "*"
            (Algebra.BigOperators.Basic.«term∏_in_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             " in "
             (Term.app `range [`k])
             ", "
             («term_/_»
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))
              "/"
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "3")))))
           "/"
           (Finset.Data.Finset.Fold.«term_*_»
            (Real.Analysis.SpecialFunctions.Trigonometric.Basic.termπ "π")
            "*"
            (Algebra.BigOperators.Basic.«term∏_in_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
             " in "
             (Term.app `range [`k])
             ", "
             («term_/_»
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "1"))
              "/"
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `i) "+" (numLit "2"))))))))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (tacticFunext__ "funext" []) [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Algebra.BigOperators.Basic.«term∏_in_,_»
                 "∏"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
                 " in "
                 (Term.app `range [`k])
                 ", "
                 («term_/_»
                  (Init.Logic.«term_+_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                    "*"
                    (Init.Coe.«term↑_» "↑" `i))
                   "+"
                   (numLit "2"))
                  "/"
                  (Init.Logic.«term_+_»
                   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                   "+"
                   (numLit "1"))))
                "="
                («term_/_»
                 (numLit "1")
                 "/"
                 (Algebra.BigOperators.Basic.«term∏_in_,_»
                  "∏"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
                  " in "
                  (Term.app `range [`k])
                  ", "
                  («term_/_»
                   (Init.Logic.«term_+_»
                    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                    "+"
                    (numLit "1"))
                   "/"
                   (Init.Logic.«term_+_»
                    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                    "+"
                    (numLit "2")))))))]
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
                    [(Tactic.rwRule [] `one_div) "," (Tactic.rwRule ["←"] `Finset.prod_inv_distrib')]
                    "]")
                   [])
                  [])
                 (group
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `prod_congr
                    [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
                  [])
                 (group (Tactic.fieldSimp "field_simp" [] [] [] [] []) [])]))))))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `prod_mul_distrib) "," (Tactic.rwRule [] `h)] "]")
           [])
          [])
         (group (Tactic.fieldSimp "field_simp" [] [] [] [] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (tacticFunext__ "funext" []) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Algebra.BigOperators.Basic.«term∏_in_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
              " in "
              (Term.app `range [`k])
              ", "
              («term_/_»
               (Init.Logic.«term_+_»
                (Finset.Data.Finset.Fold.«term_*_»
                 (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                 "*"
                 (Init.Coe.«term↑_» "↑" `i))
                "+"
                (numLit "2"))
               "/"
               (Init.Logic.«term_+_»
                (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                "+"
                (numLit "1"))))
             "="
             («term_/_»
              (numLit "1")
              "/"
              (Algebra.BigOperators.Basic.«term∏_in_,_»
               "∏"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
               " in "
               (Term.app `range [`k])
               ", "
               («term_/_»
                (Init.Logic.«term_+_»
                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                 "+"
                 (numLit "1"))
                "/"
                (Init.Logic.«term_+_»
                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
                 "+"
                 (numLit "2")))))))]
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
                 [(Tactic.rwRule [] `one_div) "," (Tactic.rwRule ["←"] `Finset.prod_inv_distrib')]
                 "]")
                [])
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `prod_congr
                 [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
               [])
              (group (Tactic.fieldSimp "field_simp" [] [] [] [] []) [])]))))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `prod_mul_distrib) "," (Tactic.rwRule [] `h)] "]")
        [])
       [])
      (group (Tactic.fieldSimp "field_simp" [] [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.fieldSimp "field_simp" [] [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.fieldSimp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `prod_mul_distrib) "," (Tactic.rwRule [] `h)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `prod_mul_distrib
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`h []]
     [(Term.typeSpec
       ":"
       («term_=_»
        (Algebra.BigOperators.Basic.«term∏_in_,_»
         "∏"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
         " in "
         (Term.app `range [`k])
         ", "
         («term_/_»
          (Init.Logic.«term_+_»
           (Finset.Data.Finset.Fold.«term_*_»
            (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
            "*"
            (Init.Coe.«term↑_» "↑" `i))
           "+"
           (numLit "2"))
          "/"
          (Init.Logic.«term_+_»
           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
           "+"
           (numLit "1"))))
        "="
        («term_/_»
         (numLit "1")
         "/"
         (Algebra.BigOperators.Basic.«term∏_in_,_»
          "∏"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
          " in "
          (Term.app `range [`k])
          ", "
          («term_/_»
           (Init.Logic.«term_+_»
            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
            "+"
            (numLit "1"))
           "/"
           (Init.Logic.«term_+_»
            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
            "+"
            (numLit "2")))))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `one_div) "," (Tactic.rwRule ["←"] `Finset.prod_inv_distrib')] "]")
           [])
          [])
         (group
          (Tactic.refine'
           "refine'"
           (Term.app
            `prod_congr
            [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
          [])
         (group (Tactic.fieldSimp "field_simp" [] [] [] [] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `one_div) "," (Tactic.rwRule ["←"] `Finset.prod_inv_distrib')] "]")
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `prod_congr
         [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
       [])
      (group (Tactic.fieldSimp "field_simp" [] [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.fieldSimp "field_simp" [] [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.fieldSimp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `prod_congr
    [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `prod_congr [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `prod_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `one_div) "," (Tactic.rwRule ["←"] `Finset.prod_inv_distrib')] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.prod_inv_distrib'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one_div
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
    " in "
    (Term.app `range [`k])
    ", "
    («term_/_»
     (Init.Logic.«term_+_»
      (Finset.Data.Finset.Fold.«term_*_»
       (Term.paren "(" [(numLit "2") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
       "*"
       (Init.Coe.«term↑_» "↑" `i))
      "+"
      (numLit "2"))
     "/"
     (Init.Logic.«term_+_»
      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
      "+"
      (numLit "1"))))
   "="
   («term_/_»
    (numLit "1")
    "/"
    (Algebra.BigOperators.Basic.«term∏_in_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
     " in "
     (Term.app `range [`k])
     ", "
     («term_/_»
      (Init.Logic.«term_+_»
       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
       "+"
       (numLit "1"))
      "/"
      (Init.Logic.«term_+_»
       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
       "+"
       (numLit "2"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   (numLit "1")
   "/"
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
    " in "
    (Term.app `range [`k])
    ", "
    («term_/_»
     (Init.Logic.«term_+_»
      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
      "+"
      (numLit "1"))
     "/"
     (Init.Logic.«term_+_»
      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
      "+"
      (numLit "2")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
   " in "
   (Term.app `range [`k])
   ", "
   («term_/_»
    (Init.Logic.«term_+_»
     (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
     "+"
     (numLit "1"))
    "/"
    (Init.Logic.«term_+_»
     (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
     "+"
     (numLit "2"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   (Init.Logic.«term_+_»
    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
    "+"
    (numLit "1"))
   "/"
   (Init.Logic.«term_+_»
    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
    "+"
    (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_»
   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
   "+"
   (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↑_» "↑" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Init.Logic.«term_+_»
   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
   "+"
   (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↑_» "↑" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_»
   (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Init.Coe.«term↑_» "↑" `i)) []] ")")
   "+"
   (numLit "1"))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `range [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
    This theorem establishes the Wallis Product for `π`. Our proof is largely about analyzing
      the behavior of the ratio of the integral of `sin x ^ n` as `n → ∞`.
      See: https://en.wikipedia.org/wiki/Wallis_product
    
      The proof can be broken down into two pieces.
      (Pieces involving general properties of the integral of `sin x ^n` can be found
      in `analysis.special_functions.integrals`.) First, we use integration by parts to obtain a
      recursive formula for `∫ x in 0..π, sin x ^ (n + 2)` in terms of `∫ x in 0..π, sin x ^ n`.
      From this we can obtain closed form products of `∫ x in 0..π, sin x ^ (2 * n)` and
      `∫ x in 0..π, sin x ^ (2 * n + 1)` via induction. Next, we study the behavior of the ratio
      `∫ (x : ℝ) in 0..π, sin x ^ (2 * k + 1)) / ∫ (x : ℝ) in 0..π, sin x ^ (2 * k)` and prove that
      it converges to one using the squeeze theorem. The final product for `π` is obtained after some
      algebraic manipulation. -/
  theorem
    tendsto_prod_pi_div_two
    : tendsto fun k => ∏ i in range k , ( 2 : ℝ ) * i + 2 / 2 * i + 1 * 2 * i + 2 / 2 * i + 3 at_top 𝓝 π / 2
    :=
      by
        suffices
            h
            : tendsto fun k => 2 / π * ∏ i in range k , ( 2 : ℝ ) * i + 2 / 2 * i + 1 * 2 * i + 2 / 2 * i + 3 at_top 𝓝 1
          ·
            have := tendsto.const_mul π / 2 h
              have h : π / 2 ≠ 0
              norm_num [ pi_ne_zero ]
              simp only [ ← mul_assocₓ , ← @ inv_div _ _ π 2 , mul_inv_cancel h , one_mulₓ , mul_oneₓ ] at this
              exact this
          have
            h
              :
                fun k : ℕ => ( 2 : ℝ ) / π * ∏ i : ℕ in range k , 2 * i + 2 / 2 * i + 1 * 2 * i + 2 / 2 * i + 3
                  =
                  fun k => 2 * ∏ i in range k , 2 * i + 2 / 2 * i + 3 / π * ∏ i : ℕ in range k , 2 * i + 1 / 2 * i + 2
              :=
              by
                funext
                  have
                    h
                      :
                        ∏ i : ℕ in range k , ( 2 : ℝ ) * ↑ i + 2 / 2 * ↑ i + 1
                          =
                          1 / ∏ i : ℕ in range k , 2 * ↑ i + 1 / 2 * ↑ i + 2
                      :=
                      by rw [ one_div , ← Finset.prod_inv_distrib' ] refine' prod_congr rfl fun x hx => _ field_simp
                  rw [ prod_mul_distrib , h ]
                  field_simp
          simp only [ h , ← integral_sin_pow_even , ← integral_sin_pow_odd ]
          exact integral_sin_pow_div_tendsto_one

end Real

