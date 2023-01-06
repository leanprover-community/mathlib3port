/-
Copyright (c) 2020 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson

! This file was ported from Lean 3 source module data.real.pi.leibniz
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! ### Leibniz's Series for Pi -/


namespace Real

open Filter Set

open Classical BigOperators TopologicalSpace Real

-- mathport name: abs
local notation "|" x "|" => abs x

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This theorem establishes **Leibniz's series for `π`**: The alternating sum of the reciprocals\n  of the odd numbers is `π/4`. Note that this is a conditionally rather than absolutely convergent\n  series. The main tool that this proof uses is the Mean Value Theorem (specifically avoiding the\n  Fundamental Theorem of Calculus).\n\n  Intuitively, the theorem holds because Leibniz's series is the Taylor series of `arctan x`\n  centered about `0` and evaluated at the value `x = 1`. Therefore, much of this proof consists of\n  reasoning about a function\n    `f := arctan x - ∑ i in finset.range k, (-(1:ℝ))^i * x^(2*i+1) / (2*i+1)`,\n  the difference between `arctan` and the `k`-th partial sum of its Taylor series. Some ingenuity is\n  required due to the fact that the Taylor series is not absolutely convergent at `x = 1`.\n\n  This proof requires a bound on `f 1`, the key idea being that `f 1` can be split as the sum of\n  `f 1 - f u` and `f u`, where `u` is a sequence of values in [0,1], carefully chosen such that\n  each of these two terms can be controlled (in different ways).\n\n  We begin the proof by (1) introducing that sequence `u` and then proving that another sequence\n  constructed from `u` tends to `0` at `+∞`. After (2) converting the limit in our goal to an\n  inequality, we (3) introduce the auxiliary function `f` defined above. Next, we (4) compute the\n  derivative of `f`, denoted by `f'`, first generally and then on each of two subintervals of [0,1].\n  We then (5) prove a bound for `f'`, again both generally as well as on each of the two\n  subintervals. Finally, we (6) apply the Mean Value Theorem twice, obtaining bounds on `f 1 - f u`\n  and `f u - f 0` from the bounds on `f'` (note that `f 0 = 0`). -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `tendsto_sum_pi_div_four [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Tendsto
         [(Term.fun
           "fun"
           (Term.basicFun
            [`k]
            []
            "=>"
            (BigOperators.Algebra.BigOperators.Basic.finset.sum
             "∑"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
             " in "
             (Term.app `Finset.range [`k])
             ", "
             («term_/_»
              («term_^_»
               («term-_»
                "-"
                (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
               "^"
               `i)
              "/"
              («term_+_» («term_*_» (num "2") "*" `i) "+" (num "1"))))))
          `atTop
          (Term.app
           (TopologicalSpace.Topology.Basic.nhds "𝓝")
           [(«term_/_»
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
             "/"
             (num "4"))])])))
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
             [(Tactic.rwRule [] `tendsto_iff_norm_tendsto_zero)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               `tendsto_zero_iff_norm_tendsto_zero)]
             "]")
            [])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `u
              []
              []
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`k]
                [(Term.typeSpec ":" (termℕ "ℕ"))]
                "=>"
                («term_^_»
                 (Term.typeAscription "(" `k ":" [`Nnreal] ")")
                 "^"
                 («term_/_»
                  («term-_» "-" (num "1"))
                  "/"
                  («term_+_»
                   («term_*_»
                    (num "2")
                    "*"
                    (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                   "+"
                   (num "1")))))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`H []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `tendsto
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`k]
                    [(Term.typeSpec ":" (termℕ "ℕ"))]
                    "=>"
                    («term_+_»
                     («term_-_»
                      (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                      "-"
                      (Term.app `u [`k]))
                     "+"
                     («term_^_»
                      (Term.app `u [`k])
                      "^"
                      («term_+_»
                       («term_*_»
                        (num "2")
                        "*"
                        (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                       "+"
                       (num "1"))))))
                  `at_top
                  (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(convert
                   "convert"
                   []
                   (Term.app
                    (Term.proj
                     (Term.app
                      (Term.proj
                       (Term.app
                        (Term.proj
                         (Term.proj
                          (Term.app
                           `tendsto_rpow_div_mul_add
                           [(«term-_» "-" (num "1")) (num "2") (num "1") `two_ne_zero.symm])
                          "."
                          `neg)
                         "."
                         `const_add)
                        [(num "1")])
                       "."
                       `add)
                      [`tendsto_inv_at_top_zero])
                     "."
                     `comp)
                    [`tendsto_coe_nat_at_top_at_top])
                   [])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Std.Tactic.Ext.«tacticExt___:_»
                     "ext"
                     [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `k))]
                     [])
                    []
                    (Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `Nnreal.coe_nat_cast)
                       ","
                       (Tactic.simpLemma [] [] `Function.comp_apply)
                       ","
                       (Tactic.simpLemma [] [] `Nnreal.coe_rpow)]
                      "]"]
                     [])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app
                         `rpow_mul
                         [(Term.app `Nat.cast_nonneg [`k])
                          («term_/_»
                           («term-_» "-" (num "1"))
                           "/"
                           («term_+_»
                            («term_*_»
                             (num "2")
                             "*"
                             (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                            "+"
                            (num "1")))
                          («term_+_»
                           («term_*_»
                            (num "2")
                            "*"
                            (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                           "+"
                           (num "1"))]))
                       ","
                       (Tactic.rwRule
                        []
                        (Term.app
                         (Term.explicit "@" `div_mul_cancel)
                         [(Term.hole "_")
                          (Term.hole "_")
                          («term_+_»
                           («term_*_»
                            (num "2")
                            "*"
                            (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                           "+"
                           (num "1"))
                          (Term.hole "_")
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                              []
                              (Tactic.simp
                               "simp"
                               []
                               []
                               ["only"]
                               ["["
                                [(Tactic.simpLemma [] [] `Nat.succ_ne_zero)
                                 ","
                                 (Tactic.simpLemma [] [] `not_false_iff)]
                                "]"]
                               [])])))]))
                       ","
                       (Tactic.rwRule [] (Term.app `rpow_neg_one [`k]))
                       ","
                       (Tactic.rwRule [] `sub_eq_add_neg)]
                      "]")
                     [])])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `add_zero)
                       ","
                       (Tactic.simpLemma [] [] `add_right_neg)]
                      "]"]
                     [])])]))))))
           []
           (Tactic.refine' "refine'" (Term.app `squeeze_zero_norm [(Term.hole "_") `H]))
           []
           (Tactic.intro "intro" [`k])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl (Term.letIdDecl `U [] [] ":=" (Term.app `u [`k]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `b
              [(Term.explicitBinder "(" [`i] [":" (termℕ "ℕ")] [] ")") `x]
              []
              ":="
              («term_/_»
               («term_*_»
                («term_^_»
                 («term-_»
                  "-"
                  (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                 "^"
                 `i)
                "*"
                («term_^_» `x "^" («term_+_» («term_*_» (num "2") "*" `i) "+" (num "1"))))
               "/"
               («term_+_» («term_*_» (num "2") "*" `i) "+" (num "1"))))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `f
              [`x]
              []
              ":="
              («term_-_»
               (Term.app `arctan [`x])
               "-"
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                " in "
                (Term.app `Finset.range [`k])
                ", "
                (Term.app `b [`i `x]))))))
           []
           (Mathlib.Tactic.tacticSuffices_
            "suffices"
            [`f_bound []]
            [(Term.typeSpec
              ":"
              («term_≤_»
               (Real.Data.Real.Pi.Leibniz.abs
                "|"
                («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [(num "0")]))
                "|")
               "≤"
               («term_+_»
                («term_-_»
                 (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 "-"
                 `U)
                "+"
                («term_^_»
                 `U
                 "^"
                 («term_+_»
                  («term_*_»
                   (num "2")
                   "*"
                   (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                  "+"
                  (num "1"))))))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_neg)]
               "]")
              [])
             []
             (convert "convert" [] `f_bound [])
             []
             (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] [])
             []
             (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `b)] "]"] [])])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hU1 []]
              [(Term.typeSpec
                ":"
                («term_≤_»
                 (Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 "≤"
                 (num "1")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Classical.«tacticBy_cases_:_» "by_cases" [`hk ":"] («term_=_» `k "=" (num "0")))
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     []
                     ["["
                      [(Tactic.simpLemma [] [] `u)
                       ","
                       (Tactic.simpLemma [] [] `U)
                       ","
                       (Tactic.simpLemma [] [] `hk)]
                      "]"]
                     [])])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.exact
                     "exact"
                     (Term.app
                      `rpow_le_one_of_one_le_of_nonpos
                      [(Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                           []
                           (Tactic.exact
                            "exact"
                            (Term.app
                             `nat.succ_le_iff.mpr
                             [(Term.app `Nat.pos_of_ne_zero [`hk])]))])))
                       (Term.app
                        `le_of_lt
                        [(Term.app
                          (Term.explicit "@" `div_neg_of_neg_of_pos)
                          [(Term.hole "_")
                           (Term.hole "_")
                           («term-_»
                            "-"
                            (Term.typeAscription
                             "("
                             (num "1")
                             ":"
                             [(Data.Real.Basic.termℝ "ℝ")]
                             ")"))
                           («term_+_» («term_*_» (num "2") "*" `k) "+" (num "1"))
                           (Term.app `neg_neg_iff_pos.mpr [`zero_lt_one])
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                               []
                               (Tactic.exact "exact" `Nat.succ_pos')])))])])]))])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`hU2 []] [] ":=" (Term.app `Nnreal.coe_nonneg [`U]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `f'
              []
              []
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
                "=>"
                («term_/_»
                 («term_^_» («term-_» "-" («term_^_» `x "^" (num "2"))) "^" `k)
                 "/"
                 («term_+_» (num "1") "+" («term_^_» `x "^" (num "2")))))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`has_deriv_at_f []]
              [(Term.typeSpec
                ":"
                (Term.forall "∀" [`x] [] "," (Term.app `HasDerivAt [`f (Term.app `f' [`x]) `x])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`x])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`has_deriv_at_b []]
                     [(Term.typeSpec
                       ":"
                       (Std.ExtendedBinder.«term∀__,_»
                        "∀"
                        (Lean.binderIdent `i)
                        («binderTerm∈_» "∈" (Term.app `Finset.range [`k]))
                        ","
                        (Term.app
                         `HasDerivAt
                         [(Term.app `b [`i])
                          («term_^_» («term-_» "-" («term_^_» `x "^" (num "2"))) "^" `i)
                          `x])))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.intro "intro" [`i `hi])
                         []
                         (convert
                          "convert"
                          []
                          (Term.app
                           `HasDerivAt.const_mul
                           [(«term_/_»
                             («term_^_»
                              (Term.typeAscription
                               "("
                               («term-_» "-" (num "1"))
                               ":"
                               [(Data.Real.Basic.termℝ "ℝ")]
                               ")")
                              "^"
                              `i)
                             "/"
                             («term_+_» («term_*_» (num "2") "*" `i) "+" (num "1")))
                            (Term.app
                             (Term.explicit "@" `HasDerivAt.pow)
                             [(Term.hole "_")
                              (Term.hole "_")
                              (Term.hole "_")
                              (Term.hole "_")
                              (Term.hole "_")
                              («term_+_» («term_*_» (num "2") "*" `i) "+" (num "1"))
                              (Term.app `has_deriv_at_id [`x])])])
                          [])
                         []
                         (tactic__
                          (cdotTk (patternIgnore (token.«· » "·")))
                          [(Std.Tactic.Ext.«tacticExt___:_»
                            "ext"
                            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))]
                            [])
                           []
                           (Tactic.simp
                            "simp"
                            []
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma [] [] `b) "," (Tactic.simpLemma [] [] `id.def)]
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
                             [(Tactic.simpLemma [] [] `Nat.add_succ_sub_one)
                              ","
                              (Tactic.simpLemma [] [] `add_zero)
                              ","
                              (Tactic.simpLemma [] [] `mul_one)
                              ","
                              (Tactic.simpLemma [] [] `id.def)
                              ","
                              (Tactic.simpLemma [] [] `Nat.cast_bit0)
                              ","
                              (Tactic.simpLemma [] [] `Nat.cast_add)
                              ","
                              (Tactic.simpLemma [] [] `Nat.cast_one)
                              ","
                              (Tactic.simpLemma [] [] `Nat.cast_mul)]
                             "]"]
                            [])
                           []
                           (Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                              ","
                              (Tactic.rwRule
                               []
                               (Term.app
                                (Term.explicit "@" `div_mul_cancel)
                                [(Term.hole "_")
                                 (Term.hole "_")
                                 («term_+_»
                                  («term_*_»
                                   (num "2")
                                   "*"
                                   (Term.typeAscription
                                    "("
                                    `i
                                    ":"
                                    [(Data.Real.Basic.termℝ "ℝ")]
                                    ")"))
                                  "+"
                                  (num "1"))
                                 (Term.hole "_")
                                 (Term.byTactic
                                  "by"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented
                                    [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                                     []
                                     (linarith "linarith" [] (linarithArgsRest [] [] []))])))]))
                              ","
                              (Tactic.rwRule [] (Term.app `pow_mul [`x (num "2") `i]))
                              ","
                              (Tactic.rwRule
                               [(patternIgnore (token.«← » "←"))]
                               (Term.app
                                `mul_pow
                                [(«term-_» "-" (num "1")) («term_^_» `x "^" (num "2")) `i]))]
                             "]")
                            [])
                           []
                           (Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])])]))))))
                  []
                  (convert
                   "convert"
                   []
                   (Term.app
                    (Term.proj (Term.app `has_deriv_at_arctan [`x]) "." `sub)
                    [(Term.app `HasDerivAt.sum [`has_deriv_at_b])])
                   [])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`g_sum []]
                     []
                     ":="
                     (Term.app
                      (Term.explicit "@" `geom_sum_eq)
                      [(Term.hole "_")
                       (Term.hole "_")
                       («term-_» "-" («term_^_» `x "^" (num "2")))
                       (Term.proj
                        (Term.app
                         (Term.proj
                          (Term.app `neg_nonpos.mpr [(Term.app `sq_nonneg [`x])])
                          "."
                          `trans_lt)
                         [`zero_lt_one])
                        "."
                        `Ne)
                       `k]))))
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `f')] "]"]
                   [(Tactic.location
                     "at"
                     (Tactic.locationHyp [`g_sum] [(patternIgnore (token.«⊢» "⊢"))]))])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `g_sum)
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `neg_add' [(«term_^_» `x "^" (num "2")) (num "1")]))
                     ","
                     (Tactic.rwRule
                      []
                      (Term.app `add_comm [(«term_^_» `x "^" (num "2")) (num "1")]))
                     ","
                     (Tactic.rwRule [] `sub_eq_add_neg)
                     ","
                     (Tactic.rwRule [] `neg_div')
                     ","
                     (Tactic.rwRule [] `neg_div_neg_eq)]
                    "]")
                   [])
                  []
                  (Mathlib.Tactic.RingNF.ring "ring")]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hderiv1 []]
              [(Term.typeSpec
                ":"
                (Std.ExtendedBinder.«term∀__,_»
                 "∀"
                 (Lean.binderIdent `x)
                 («binderTerm∈_»
                  "∈"
                  (Term.app
                   `Icc
                   [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
                 ","
                 (Term.app
                  `HasDerivWithinAt
                  [`f
                   (Term.app `f' [`x])
                   (Term.app
                    `Icc
                    [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")])
                   `x])))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`x `hx]
                []
                "=>"
                (Term.proj (Term.app `has_deriv_at_f [`x]) "." `HasDerivWithinAt))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hderiv2 []]
              [(Term.typeSpec
                ":"
                (Std.ExtendedBinder.«term∀__,_»
                 "∀"
                 (Lean.binderIdent `x)
                 («binderTerm∈_»
                  "∈"
                  (Term.app
                   `Icc
                   [(num "0") (Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
                 ","
                 (Term.app
                  `HasDerivWithinAt
                  [`f
                   (Term.app `f' [`x])
                   (Term.app
                    `Icc
                    [(num "0") (Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
                   `x])))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`x `hx]
                []
                "=>"
                (Term.proj (Term.app `has_deriv_at_f [`x]) "." `HasDerivWithinAt))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`f'_bound []]
              [(Term.typeSpec
                ":"
                (Std.ExtendedBinder.«term∀__,_»
                 "∀"
                 (Lean.binderIdent `x)
                 («binderTerm∈_»
                  "∈"
                  (Term.app
                   `Icc
                   [(Term.typeAscription
                     "("
                     («term-_» "-" (num "1"))
                     ":"
                     [(Data.Real.Basic.termℝ "ℝ")]
                     ")")
                    (num "1")]))
                 ","
                 («term_≤_»
                  (Real.Data.Real.Pi.Leibniz.abs "|" (Term.app `f' [`x]) "|")
                  "≤"
                  («term_^_»
                   (Real.Data.Real.Pi.Leibniz.abs "|" `x "|")
                   "^"
                   («term_*_» (num "2") "*" `k)))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`x `hx])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `abs_div)
                     ","
                     (Tactic.rwRule
                      []
                      (Term.app
                       `IsAbsoluteValue.abv_pow
                       [`abs («term-_» "-" («term_^_» `x "^" (num "2"))) `k]))
                     ","
                     (Tactic.rwRule [] `abs_neg)
                     ","
                     (Tactic.rwRule [] (Term.app `IsAbsoluteValue.abv_pow [`abs `x (num "2")]))
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_mul)]
                    "]")
                   [])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `div_le_of_nonneg_of_le_mul
                    [(Term.app `abs_nonneg [(Term.hole "_")])
                     (Term.app
                      `pow_nonneg
                      [(Term.app `abs_nonneg [(Term.hole "_")]) (Term.hole "_")])
                     (Term.hole "_")]))
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `le_mul_of_one_le_right
                    [(Term.app
                      `pow_nonneg
                      [(Term.app `abs_nonneg [(Term.hole "_")]) (Term.hole "_")])
                     (Term.hole "_")]))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      []
                      (Term.app
                       `abs_of_nonneg
                       [(Term.typeAscription
                         "("
                         (Term.app `add_nonneg [`zero_le_one (Term.app `sq_nonneg [`x])])
                         ":"
                         [(«term_≤_»
                           (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                           "≤"
                           (Term.hole "_"))]
                         ")")]))]
                    "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.typeAscription
                    "("
                    (Term.app `le_add_of_nonneg_right [(Term.app `sq_nonneg [`x])])
                    ":"
                    [(«term_≤_»
                      (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                      "≤"
                      (Term.hole "_"))]
                    ")"))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hbound1 []]
              [(Term.typeSpec
                ":"
                (Std.ExtendedBinder.«term∀__,_»
                 "∀"
                 (Lean.binderIdent `x)
                 («binderTerm∈_»
                  "∈"
                  (Term.app
                   `Ico
                   [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
                 ","
                 («term_≤_»
                  (Real.Data.Real.Pi.Leibniz.abs "|" (Term.app `f' [`x]) "|")
                  "≤"
                  (num "1"))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
                    (Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `hx_left)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `hx_right)])
                        [])]
                      "⟩"))]
                   [])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hincr []]
                     []
                     ":="
                     (Term.app
                      `pow_le_pow_of_le_left
                      [(Term.app `le_trans [`hU2 `hx_left])
                       (Term.app `le_of_lt [`hx_right])
                       («term_*_» (num "2") "*" `k)]))))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `one_pow [(«term_*_» (num "2") "*" `k)]))
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `abs_of_nonneg [(Term.app `le_trans [`hU2 `hx_left])]))]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hincr] []))])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `abs_of_nonneg [(Term.app `le_trans [`hU2 `hx_left])]))]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hx_right] []))])
                  []
                  (linarith
                   "linarith"
                   []
                   (linarithArgsRest
                    []
                    []
                    ["["
                     [(Term.app
                       `f'_bound
                       [`x
                        (Term.app
                         `mem_Icc.mpr
                         [(Term.app `abs_le.mp [(Term.app `le_of_lt [`hx_right])])])])]
                     "]"]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hbound2 []]
              [(Term.typeSpec
                ":"
                (Std.ExtendedBinder.«term∀__,_»
                 "∀"
                 (Lean.binderIdent `x)
                 («binderTerm∈_»
                  "∈"
                  (Term.app
                   `Ico
                   [(num "0") (Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
                 ","
                 («term_≤_»
                  (Real.Data.Real.Pi.Leibniz.abs "|" (Term.app `f' [`x]) "|")
                  "≤"
                  («term_^_» `U "^" («term_*_» (num "2") "*" `k)))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
                    (Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `hx_left)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `hx_right)])
                        [])]
                      "⟩"))]
                   [])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hincr []]
                     []
                     ":="
                     (Term.app
                      `pow_le_pow_of_le_left
                      [`hx_left (Term.app `le_of_lt [`hx_right]) («term_*_» (num "2") "*" `k)]))))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `abs_of_nonneg [`hx_left]))]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hincr `hx_right] []))])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `abs_of_nonneg [`hU2]))]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hU1 `hx_right] []))])
                  []
                  (linarith
                   "linarith"
                   []
                   (linarithArgsRest
                    []
                    []
                    ["["
                     [(Term.app
                       `f'_bound
                       [`x
                        (Term.app
                         `mem_Icc.mpr
                         [(Term.app
                           `abs_le.mp
                           [(Term.app `le_trans [(Term.app `le_of_lt [`hx_right]) `hU1])])])])]
                     "]"]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`mvt1 []]
              []
              ":="
              (Term.app
               `norm_image_sub_le_of_norm_deriv_le_segment'
               [`hderiv1 `hbound1 (Term.hole "_") (Term.app `right_mem_Icc.mpr [`hU1])]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`mvt2 []]
              []
              ":="
              (Term.app
               `norm_image_sub_le_of_norm_deriv_le_segment'
               [`hderiv2 `hbound2 (Term.hole "_") (Term.app `right_mem_Icc.mpr [`hU2])]))))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (Real.Data.Real.Pi.Leibniz.abs
               "|"
               («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [(num "0")]))
               "|")
              "="
              (Real.Data.Real.Pi.Leibniz.abs
               "|"
               («term_+_»
                («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
                "+"
                («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")])))
               "|"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])]))))
            [(calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_+_»
                («term_*_» (num "1") "*" («term_-_» (num "1") "-" `U))
                "+"
                («term_*_»
                 («term_^_» `U "^" («term_*_» (num "2") "*" `k))
                 "*"
                 («term_-_» `U "-" (num "0")))))
              ":="
              (Term.app
               `le_trans
               [(Term.app
                 `abs_add
                 [(«term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
                  («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")]))])
                (Term.app `add_le_add [`mvt1 `mvt2])]))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_+_»
                («term_-_» (num "1") "-" `U)
                "+"
                («term_*_» («term_^_» `U "^" («term_*_» (num "2") "*" `k)) "*" `U)))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_+_»
                («term_-_» (num "1") "-" (Term.app `u [`k]))
                "+"
                («term_^_»
                 (Term.app `u [`k])
                 "^"
                 («term_+_»
                  («term_*_»
                   (num "2")
                   "*"
                   (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                  "+"
                  (num "1")))))
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
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       `pow_succ'
                       [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                        («term_*_» (num "2") "*" `k)]))]
                    "]")
                   [])
                  []
                  (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])]))))])])))
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
            [(Tactic.rwRule [] `tendsto_iff_norm_tendsto_zero)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `tendsto_zero_iff_norm_tendsto_zero)]
            "]")
           [])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `u
             []
             []
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`k]
               [(Term.typeSpec ":" (termℕ "ℕ"))]
               "=>"
               («term_^_»
                (Term.typeAscription "(" `k ":" [`Nnreal] ")")
                "^"
                («term_/_»
                 («term-_» "-" (num "1"))
                 "/"
                 («term_+_»
                  («term_*_»
                   (num "2")
                   "*"
                   (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                  "+"
                  (num "1")))))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`H []]
             [(Term.typeSpec
               ":"
               (Term.app
                `tendsto
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`k]
                   [(Term.typeSpec ":" (termℕ "ℕ"))]
                   "=>"
                   («term_+_»
                    («term_-_»
                     (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                     "-"
                     (Term.app `u [`k]))
                    "+"
                    («term_^_»
                     (Term.app `u [`k])
                     "^"
                     («term_+_»
                      («term_*_»
                       (num "2")
                       "*"
                       (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                      "+"
                      (num "1"))))))
                 `at_top
                 (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(convert
                  "convert"
                  []
                  (Term.app
                   (Term.proj
                    (Term.app
                     (Term.proj
                      (Term.app
                       (Term.proj
                        (Term.proj
                         (Term.app
                          `tendsto_rpow_div_mul_add
                          [(«term-_» "-" (num "1")) (num "2") (num "1") `two_ne_zero.symm])
                         "."
                         `neg)
                        "."
                        `const_add)
                       [(num "1")])
                      "."
                      `add)
                     [`tendsto_inv_at_top_zero])
                    "."
                    `comp)
                   [`tendsto_coe_nat_at_top_at_top])
                  [])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Std.Tactic.Ext.«tacticExt___:_»
                    "ext"
                    [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `k))]
                    [])
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `Nnreal.coe_nat_cast)
                      ","
                      (Tactic.simpLemma [] [] `Function.comp_apply)
                      ","
                      (Tactic.simpLemma [] [] `Nnreal.coe_rpow)]
                     "]"]
                    [])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app
                        `rpow_mul
                        [(Term.app `Nat.cast_nonneg [`k])
                         («term_/_»
                          («term-_» "-" (num "1"))
                          "/"
                          («term_+_»
                           («term_*_»
                            (num "2")
                            "*"
                            (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                           "+"
                           (num "1")))
                         («term_+_»
                          («term_*_»
                           (num "2")
                           "*"
                           (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                          "+"
                          (num "1"))]))
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app
                        (Term.explicit "@" `div_mul_cancel)
                        [(Term.hole "_")
                         (Term.hole "_")
                         («term_+_»
                          («term_*_»
                           (num "2")
                           "*"
                           (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                          "+"
                          (num "1"))
                         (Term.hole "_")
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                             []
                             (Tactic.simp
                              "simp"
                              []
                              []
                              ["only"]
                              ["["
                               [(Tactic.simpLemma [] [] `Nat.succ_ne_zero)
                                ","
                                (Tactic.simpLemma [] [] `not_false_iff)]
                               "]"]
                              [])])))]))
                      ","
                      (Tactic.rwRule [] (Term.app `rpow_neg_one [`k]))
                      ","
                      (Tactic.rwRule [] `sub_eq_add_neg)]
                     "]")
                    [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `add_zero)
                      ","
                      (Tactic.simpLemma [] [] `add_right_neg)]
                     "]"]
                    [])])]))))))
          []
          (Tactic.refine' "refine'" (Term.app `squeeze_zero_norm [(Term.hole "_") `H]))
          []
          (Tactic.intro "intro" [`k])
          []
          (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `U [] [] ":=" (Term.app `u [`k]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `b
             [(Term.explicitBinder "(" [`i] [":" (termℕ "ℕ")] [] ")") `x]
             []
             ":="
             («term_/_»
              («term_*_»
               («term_^_»
                («term-_»
                 "-"
                 (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                "^"
                `i)
               "*"
               («term_^_» `x "^" («term_+_» («term_*_» (num "2") "*" `i) "+" (num "1"))))
              "/"
              («term_+_» («term_*_» (num "2") "*" `i) "+" (num "1"))))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `f
             [`x]
             []
             ":="
             («term_-_»
              (Term.app `arctan [`x])
              "-"
              (BigOperators.Algebra.BigOperators.Basic.finset.sum
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               " in "
               (Term.app `Finset.range [`k])
               ", "
               (Term.app `b [`i `x]))))))
          []
          (Mathlib.Tactic.tacticSuffices_
           "suffices"
           [`f_bound []]
           [(Term.typeSpec
             ":"
             («term_≤_»
              (Real.Data.Real.Pi.Leibniz.abs
               "|"
               («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [(num "0")]))
               "|")
              "≤"
              («term_+_»
               («term_-_»
                (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                "-"
                `U)
               "+"
               («term_^_»
                `U
                "^"
                («term_+_»
                 («term_*_»
                  (num "2")
                  "*"
                  (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                 "+"
                 (num "1"))))))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_neg)]
              "]")
             [])
            []
            (convert "convert" [] `f_bound [])
            []
            (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] [])
            []
            (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `b)] "]"] [])])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hU1 []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                (Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                "≤"
                (num "1")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Classical.«tacticBy_cases_:_» "by_cases" [`hk ":"] («term_=_» `k "=" (num "0")))
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["["
                     [(Tactic.simpLemma [] [] `u)
                      ","
                      (Tactic.simpLemma [] [] `U)
                      ","
                      (Tactic.simpLemma [] [] `hk)]
                     "]"]
                    [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app
                     `rpow_le_one_of_one_le_of_nonpos
                     [(Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                          []
                          (Tactic.exact
                           "exact"
                           (Term.app
                            `nat.succ_le_iff.mpr
                            [(Term.app `Nat.pos_of_ne_zero [`hk])]))])))
                      (Term.app
                       `le_of_lt
                       [(Term.app
                         (Term.explicit "@" `div_neg_of_neg_of_pos)
                         [(Term.hole "_")
                          (Term.hole "_")
                          («term-_»
                           "-"
                           (Term.typeAscription
                            "("
                            (num "1")
                            ":"
                            [(Data.Real.Basic.termℝ "ℝ")]
                            ")"))
                          («term_+_» («term_*_» (num "2") "*" `k) "+" (num "1"))
                          (Term.app `neg_neg_iff_pos.mpr [`zero_lt_one])
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                              []
                              (Tactic.exact "exact" `Nat.succ_pos')])))])])]))])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`hU2 []] [] ":=" (Term.app `Nnreal.coe_nonneg [`U]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `f'
             []
             []
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`x]
               [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
               "=>"
               («term_/_»
                («term_^_» («term-_» "-" («term_^_» `x "^" (num "2"))) "^" `k)
                "/"
                («term_+_» (num "1") "+" («term_^_» `x "^" (num "2")))))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`has_deriv_at_f []]
             [(Term.typeSpec
               ":"
               (Term.forall "∀" [`x] [] "," (Term.app `HasDerivAt [`f (Term.app `f' [`x]) `x])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`x])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`has_deriv_at_b []]
                    [(Term.typeSpec
                      ":"
                      (Std.ExtendedBinder.«term∀__,_»
                       "∀"
                       (Lean.binderIdent `i)
                       («binderTerm∈_» "∈" (Term.app `Finset.range [`k]))
                       ","
                       (Term.app
                        `HasDerivAt
                        [(Term.app `b [`i])
                         («term_^_» («term-_» "-" («term_^_» `x "^" (num "2"))) "^" `i)
                         `x])))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.intro "intro" [`i `hi])
                        []
                        (convert
                         "convert"
                         []
                         (Term.app
                          `HasDerivAt.const_mul
                          [(«term_/_»
                            («term_^_»
                             (Term.typeAscription
                              "("
                              («term-_» "-" (num "1"))
                              ":"
                              [(Data.Real.Basic.termℝ "ℝ")]
                              ")")
                             "^"
                             `i)
                            "/"
                            («term_+_» («term_*_» (num "2") "*" `i) "+" (num "1")))
                           (Term.app
                            (Term.explicit "@" `HasDerivAt.pow)
                            [(Term.hole "_")
                             (Term.hole "_")
                             (Term.hole "_")
                             (Term.hole "_")
                             (Term.hole "_")
                             («term_+_» («term_*_» (num "2") "*" `i) "+" (num "1"))
                             (Term.app `has_deriv_at_id [`x])])])
                         [])
                        []
                        (tactic__
                         (cdotTk (patternIgnore (token.«· » "·")))
                         [(Std.Tactic.Ext.«tacticExt___:_»
                           "ext"
                           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))]
                           [])
                          []
                          (Tactic.simp
                           "simp"
                           []
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `b) "," (Tactic.simpLemma [] [] `id.def)]
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
                            [(Tactic.simpLemma [] [] `Nat.add_succ_sub_one)
                             ","
                             (Tactic.simpLemma [] [] `add_zero)
                             ","
                             (Tactic.simpLemma [] [] `mul_one)
                             ","
                             (Tactic.simpLemma [] [] `id.def)
                             ","
                             (Tactic.simpLemma [] [] `Nat.cast_bit0)
                             ","
                             (Tactic.simpLemma [] [] `Nat.cast_add)
                             ","
                             (Tactic.simpLemma [] [] `Nat.cast_one)
                             ","
                             (Tactic.simpLemma [] [] `Nat.cast_mul)]
                            "]"]
                           [])
                          []
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                             ","
                             (Tactic.rwRule
                              []
                              (Term.app
                               (Term.explicit "@" `div_mul_cancel)
                               [(Term.hole "_")
                                (Term.hole "_")
                                («term_+_»
                                 («term_*_»
                                  (num "2")
                                  "*"
                                  (Term.typeAscription
                                   "("
                                   `i
                                   ":"
                                   [(Data.Real.Basic.termℝ "ℝ")]
                                   ")"))
                                 "+"
                                 (num "1"))
                                (Term.hole "_")
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                                    []
                                    (linarith "linarith" [] (linarithArgsRest [] [] []))])))]))
                             ","
                             (Tactic.rwRule [] (Term.app `pow_mul [`x (num "2") `i]))
                             ","
                             (Tactic.rwRule
                              [(patternIgnore (token.«← » "←"))]
                              (Term.app
                               `mul_pow
                               [(«term-_» "-" (num "1")) («term_^_» `x "^" (num "2")) `i]))]
                            "]")
                           [])
                          []
                          (Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])])]))))))
                 []
                 (convert
                  "convert"
                  []
                  (Term.app
                   (Term.proj (Term.app `has_deriv_at_arctan [`x]) "." `sub)
                   [(Term.app `HasDerivAt.sum [`has_deriv_at_b])])
                  [])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`g_sum []]
                    []
                    ":="
                    (Term.app
                     (Term.explicit "@" `geom_sum_eq)
                     [(Term.hole "_")
                      (Term.hole "_")
                      («term-_» "-" («term_^_» `x "^" (num "2")))
                      (Term.proj
                       (Term.app
                        (Term.proj
                         (Term.app `neg_nonpos.mpr [(Term.app `sq_nonneg [`x])])
                         "."
                         `trans_lt)
                        [`zero_lt_one])
                       "."
                       `Ne)
                      `k]))))
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `f')] "]"]
                  [(Tactic.location
                    "at"
                    (Tactic.locationHyp [`g_sum] [(patternIgnore (token.«⊢» "⊢"))]))])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `g_sum)
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `neg_add' [(«term_^_» `x "^" (num "2")) (num "1")]))
                    ","
                    (Tactic.rwRule [] (Term.app `add_comm [(«term_^_» `x "^" (num "2")) (num "1")]))
                    ","
                    (Tactic.rwRule [] `sub_eq_add_neg)
                    ","
                    (Tactic.rwRule [] `neg_div')
                    ","
                    (Tactic.rwRule [] `neg_div_neg_eq)]
                   "]")
                  [])
                 []
                 (Mathlib.Tactic.RingNF.ring "ring")]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hderiv1 []]
             [(Term.typeSpec
               ":"
               (Std.ExtendedBinder.«term∀__,_»
                "∀"
                (Lean.binderIdent `x)
                («binderTerm∈_»
                 "∈"
                 (Term.app
                  `Icc
                  [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
                ","
                (Term.app
                 `HasDerivWithinAt
                 [`f
                  (Term.app `f' [`x])
                  (Term.app
                   `Icc
                   [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")])
                  `x])))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`x `hx]
               []
               "=>"
               (Term.proj (Term.app `has_deriv_at_f [`x]) "." `HasDerivWithinAt))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hderiv2 []]
             [(Term.typeSpec
               ":"
               (Std.ExtendedBinder.«term∀__,_»
                "∀"
                (Lean.binderIdent `x)
                («binderTerm∈_»
                 "∈"
                 (Term.app
                  `Icc
                  [(num "0") (Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
                ","
                (Term.app
                 `HasDerivWithinAt
                 [`f
                  (Term.app `f' [`x])
                  (Term.app
                   `Icc
                   [(num "0") (Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
                  `x])))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`x `hx]
               []
               "=>"
               (Term.proj (Term.app `has_deriv_at_f [`x]) "." `HasDerivWithinAt))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`f'_bound []]
             [(Term.typeSpec
               ":"
               (Std.ExtendedBinder.«term∀__,_»
                "∀"
                (Lean.binderIdent `x)
                («binderTerm∈_»
                 "∈"
                 (Term.app
                  `Icc
                  [(Term.typeAscription
                    "("
                    («term-_» "-" (num "1"))
                    ":"
                    [(Data.Real.Basic.termℝ "ℝ")]
                    ")")
                   (num "1")]))
                ","
                («term_≤_»
                 (Real.Data.Real.Pi.Leibniz.abs "|" (Term.app `f' [`x]) "|")
                 "≤"
                 («term_^_»
                  (Real.Data.Real.Pi.Leibniz.abs "|" `x "|")
                  "^"
                  («term_*_» (num "2") "*" `k)))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`x `hx])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `abs_div)
                    ","
                    (Tactic.rwRule
                     []
                     (Term.app
                      `IsAbsoluteValue.abv_pow
                      [`abs («term-_» "-" («term_^_» `x "^" (num "2"))) `k]))
                    ","
                    (Tactic.rwRule [] `abs_neg)
                    ","
                    (Tactic.rwRule [] (Term.app `IsAbsoluteValue.abv_pow [`abs `x (num "2")]))
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `pow_mul)]
                   "]")
                  [])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `div_le_of_nonneg_of_le_mul
                   [(Term.app `abs_nonneg [(Term.hole "_")])
                    (Term.app
                     `pow_nonneg
                     [(Term.app `abs_nonneg [(Term.hole "_")]) (Term.hole "_")])
                    (Term.hole "_")]))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `le_mul_of_one_le_right
                   [(Term.app
                     `pow_nonneg
                     [(Term.app `abs_nonneg [(Term.hole "_")]) (Term.hole "_")])
                    (Term.hole "_")]))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app
                      `abs_of_nonneg
                      [(Term.typeAscription
                        "("
                        (Term.app `add_nonneg [`zero_le_one (Term.app `sq_nonneg [`x])])
                        ":"
                        [(«term_≤_»
                          (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                          "≤"
                          (Term.hole "_"))]
                        ")")]))]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.typeAscription
                   "("
                   (Term.app `le_add_of_nonneg_right [(Term.app `sq_nonneg [`x])])
                   ":"
                   [(«term_≤_»
                     (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                     "≤"
                     (Term.hole "_"))]
                   ")"))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hbound1 []]
             [(Term.typeSpec
               ":"
               (Std.ExtendedBinder.«term∀__,_»
                "∀"
                (Lean.binderIdent `x)
                («binderTerm∈_»
                 "∈"
                 (Term.app
                  `Ico
                  [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
                ","
                («term_≤_»
                 (Real.Data.Real.Pi.Leibniz.abs "|" (Term.app `f' [`x]) "|")
                 "≤"
                 (num "1"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx_left)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `hx_right)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hincr []]
                    []
                    ":="
                    (Term.app
                     `pow_le_pow_of_le_left
                     [(Term.app `le_trans [`hU2 `hx_left])
                      (Term.app `le_of_lt [`hx_right])
                      («term_*_» (num "2") "*" `k)]))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `one_pow [(«term_*_» (num "2") "*" `k)]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `abs_of_nonneg [(Term.app `le_trans [`hU2 `hx_left])]))]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hincr] []))])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `abs_of_nonneg [(Term.app `le_trans [`hU2 `hx_left])]))]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hx_right] []))])
                 []
                 (linarith
                  "linarith"
                  []
                  (linarithArgsRest
                   []
                   []
                   ["["
                    [(Term.app
                      `f'_bound
                      [`x
                       (Term.app
                        `mem_Icc.mpr
                        [(Term.app `abs_le.mp [(Term.app `le_of_lt [`hx_right])])])])]
                    "]"]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hbound2 []]
             [(Term.typeSpec
               ":"
               (Std.ExtendedBinder.«term∀__,_»
                "∀"
                (Lean.binderIdent `x)
                («binderTerm∈_»
                 "∈"
                 (Term.app
                  `Ico
                  [(num "0") (Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
                ","
                («term_≤_»
                 (Real.Data.Real.Pi.Leibniz.abs "|" (Term.app `f' [`x]) "|")
                 "≤"
                 («term_^_» `U "^" («term_*_» (num "2") "*" `k)))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx_left)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `hx_right)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hincr []]
                    []
                    ":="
                    (Term.app
                     `pow_le_pow_of_le_left
                     [`hx_left (Term.app `le_of_lt [`hx_right]) («term_*_» (num "2") "*" `k)]))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `abs_of_nonneg [`hx_left]))]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hincr `hx_right] []))])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `abs_of_nonneg [`hU2]))]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hU1 `hx_right] []))])
                 []
                 (linarith
                  "linarith"
                  []
                  (linarithArgsRest
                   []
                   []
                   ["["
                    [(Term.app
                      `f'_bound
                      [`x
                       (Term.app
                        `mem_Icc.mpr
                        [(Term.app
                          `abs_le.mp
                          [(Term.app `le_trans [(Term.app `le_of_lt [`hx_right]) `hU1])])])])]
                    "]"]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`mvt1 []]
             []
             ":="
             (Term.app
              `norm_image_sub_le_of_norm_deriv_le_segment'
              [`hderiv1 `hbound1 (Term.hole "_") (Term.app `right_mem_Icc.mpr [`hU1])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`mvt2 []]
             []
             ":="
             (Term.app
              `norm_image_sub_le_of_norm_deriv_le_segment'
              [`hderiv2 `hbound2 (Term.hole "_") (Term.app `right_mem_Icc.mpr [`hU2])]))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (Real.Data.Real.Pi.Leibniz.abs
              "|"
              («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [(num "0")]))
              "|")
             "="
             (Real.Data.Real.Pi.Leibniz.abs
              "|"
              («term_+_»
               («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
               "+"
               («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")])))
              "|"))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])]))))
           [(calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_+_»
               («term_*_» (num "1") "*" («term_-_» (num "1") "-" `U))
               "+"
               («term_*_»
                («term_^_» `U "^" («term_*_» (num "2") "*" `k))
                "*"
                («term_-_» `U "-" (num "0")))))
             ":="
             (Term.app
              `le_trans
              [(Term.app
                `abs_add
                [(«term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
                 («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")]))])
               (Term.app `add_le_add [`mvt1 `mvt2])]))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               («term_-_» (num "1") "-" `U)
               "+"
               («term_*_» («term_^_» `U "^" («term_*_» (num "2") "*" `k)) "*" `U)))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               («term_-_» (num "1") "-" (Term.app `u [`k]))
               "+"
               («term_^_»
                (Term.app `u [`k])
                "^"
                («term_+_»
                 («term_*_»
                  (num "2")
                  "*"
                  (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
                 "+"
                 (num "1")))))
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
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `pow_succ'
                      [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                       («term_*_» (num "2") "*" `k)]))]
                   "]")
                  [])
                 []
                 (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Real.Data.Real.Pi.Leibniz.abs
          "|"
          («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [(num "0")]))
          "|")
         "="
         (Real.Data.Real.Pi.Leibniz.abs
          "|"
          («term_+_»
           («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
           "+"
           («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")])))
          "|"))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])]))))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_»
           («term_*_» (num "1") "*" («term_-_» (num "1") "-" `U))
           "+"
           («term_*_»
            («term_^_» `U "^" («term_*_» (num "2") "*" `k))
            "*"
            («term_-_» `U "-" (num "0")))))
         ":="
         (Term.app
          `le_trans
          [(Term.app
            `abs_add
            [(«term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
             («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")]))])
           (Term.app `add_le_add [`mvt1 `mvt2])]))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           («term_-_» (num "1") "-" `U)
           "+"
           («term_*_» («term_^_» `U "^" («term_*_» (num "2") "*" `k)) "*" `U)))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           («term_-_» (num "1") "-" (Term.app `u [`k]))
           "+"
           («term_^_»
            (Term.app `u [`k])
            "^"
            («term_+_»
             («term_*_»
              (num "2")
              "*"
              (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
             "+"
             (num "1")))))
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
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  `pow_succ'
                  [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                   («term_*_» (num "2") "*" `k)]))]
               "]")
              [])
             []
             (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])]))))])
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
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `pow_succ'
               [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                («term_*_» (num "2") "*" `k)]))]
            "]")
           [])
          []
          (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `pow_succ'
           [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
            («term_*_» (num "2") "*" `k)]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `pow_succ'
       [(Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
        («term_*_» (num "2") "*" `k)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» (num "2") "*" `k) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `U ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_succ'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_+_»
        («term_-_» (num "1") "-" (Term.app `u [`k]))
        "+"
        («term_^_»
         (Term.app `u [`k])
         "^"
         («term_+_»
          («term_*_»
           (num "2")
           "*"
           (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
          "+"
          (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_-_» (num "1") "-" (Term.app `u [`k]))
       "+"
       («term_^_»
        (Term.app `u [`k])
        "^"
        («term_+_»
         («term_*_»
          (num "2")
          "*"
          (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
         "+"
         (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.app `u [`k])
       "^"
       («term_+_»
        («term_*_» (num "2") "*" (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
        "+"
        (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_*_» (num "2") "*" (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
       "+"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» (num "2") "*" (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      («term_*_» (num "2") "*" (Term.typeAscription "(" `k ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
      "+"
      (num "1"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `u [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_-_» (num "1") "-" (Term.app `u [`k]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `u [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_+_»
        («term_-_» (num "1") "-" `U)
        "+"
        («term_*_» («term_^_» `U "^" («term_*_» (num "2") "*" `k)) "*" `U)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_-_» (num "1") "-" `U)
       "+"
       («term_*_» («term_^_» `U "^" («term_*_» (num "2") "*" `k)) "*" `U))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_^_» `U "^" («term_*_» (num "2") "*" `k)) "*" `U)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `U "^" («term_*_» (num "2") "*" `k))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» (num "2") "*" `k) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `U
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_-_» (num "1") "-" `U)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app
       `le_trans
       [(Term.app
         `abs_add
         [(«term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
          («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")]))])
        (Term.app `add_le_add [`mvt1 `mvt2])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_le_add [`mvt1 `mvt2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mvt2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mvt1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_le_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `add_le_add [`mvt1 `mvt2])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `abs_add
       [(«term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
        («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `abs_add
      [(Term.paren "(" («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U])) ")")
       (Term.paren "(" («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")])) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_+_»
        («term_*_» (num "1") "*" («term_-_» (num "1") "-" `U))
        "+"
        («term_*_»
         («term_^_» `U "^" («term_*_» (num "2") "*" `k))
         "*"
         («term_-_» `U "-" (num "0")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_*_» (num "1") "*" («term_-_» (num "1") "-" `U))
       "+"
       («term_*_» («term_^_» `U "^" («term_*_» (num "2") "*" `k)) "*" («term_-_» `U "-" (num "0"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_^_» `U "^" («term_*_» (num "2") "*" `k)) "*" («term_-_» `U "-" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `U "-" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `U
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `U "-" (num "0")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» `U "^" («term_*_» (num "2") "*" `k))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» (num "2") "*" `k) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `U
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» (num "1") "*" («term_-_» (num "1") "-" `U))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (num "1") "-" `U)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» (num "1") "-" `U) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Real.Data.Real.Pi.Leibniz.abs
        "|"
        («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [(num "0")]))
        "|")
       "="
       (Real.Data.Real.Pi.Leibniz.abs
        "|"
        («term_+_»
         («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
         "+"
         («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")])))
        "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Real.Data.Real.Pi.Leibniz.abs
       "|"
       («term_+_»
        («term_-_» (Term.app `f [(num "1")]) "-" (Term.app `f [`U]))
        "+"
        («term_-_» (Term.app `f [`U]) "-" (Term.app `f [(num "0")])))
       "|")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Real.Data.Real.Pi.Leibniz.abs', expected 'Real.Data.Real.Pi.Leibniz.abs._@.Data.Real.Pi.Leibniz._hyg.7'
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
    This theorem establishes **Leibniz's series for `π`**: The alternating sum of the reciprocals
      of the odd numbers is `π/4`. Note that this is a conditionally rather than absolutely convergent
      series. The main tool that this proof uses is the Mean Value Theorem (specifically avoiding the
      Fundamental Theorem of Calculus).
    
      Intuitively, the theorem holds because Leibniz's series is the Taylor series of `arctan x`
      centered about `0` and evaluated at the value `x = 1`. Therefore, much of this proof consists of
      reasoning about a function
        `f := arctan x - ∑ i in finset.range k, (-(1:ℝ))^i * x^(2*i+1) / (2*i+1)`,
      the difference between `arctan` and the `k`-th partial sum of its Taylor series. Some ingenuity is
      required due to the fact that the Taylor series is not absolutely convergent at `x = 1`.
    
      This proof requires a bound on `f 1`, the key idea being that `f 1` can be split as the sum of
      `f 1 - f u` and `f u`, where `u` is a sequence of values in [0,1], carefully chosen such that
      each of these two terms can be controlled (in different ways).
    
      We begin the proof by (1) introducing that sequence `u` and then proving that another sequence
      constructed from `u` tends to `0` at `+∞`. After (2) converting the limit in our goal to an
      inequality, we (3) introduce the auxiliary function `f` defined above. Next, we (4) compute the
      derivative of `f`, denoted by `f'`, first generally and then on each of two subintervals of [0,1].
      We then (5) prove a bound for `f'`, again both generally as well as on each of the two
      subintervals. Finally, we (6) apply the Mean Value Theorem twice, obtaining bounds on `f 1 - f u`
      and `f u - f 0` from the bounds on `f'` (note that `f 0 = 0`). -/
  theorem
    tendsto_sum_pi_div_four
    : Tendsto fun k => ∑ i in Finset.range k , - ( 1 : ℝ ) ^ i / 2 * i + 1 atTop 𝓝 π / 4
    :=
      by
        rw [ tendsto_iff_norm_tendsto_zero , ← tendsto_zero_iff_norm_tendsto_zero ]
          let u := fun k : ℕ => ( k : Nnreal ) ^ - 1 / 2 * ( k : ℝ ) + 1
          have
            H
              : tendsto fun k : ℕ => ( 1 : ℝ ) - u k + u k ^ 2 * ( k : ℝ ) + 1 at_top 𝓝 0
              :=
              by
                convert
                    tendsto_rpow_div_mul_add - 1 2 1 two_ne_zero.symm . neg . const_add 1 . add
                          tendsto_inv_at_top_zero
                        .
                        comp
                      tendsto_coe_nat_at_top_at_top
                  ·
                    ext k
                      simp only [ Nnreal.coe_nat_cast , Function.comp_apply , Nnreal.coe_rpow ]
                      rw
                        [
                          ← rpow_mul Nat.cast_nonneg k - 1 / 2 * ( k : ℝ ) + 1 2 * ( k : ℝ ) + 1
                            ,
                            @ div_mul_cancel
                              _
                                _
                                2 * ( k : ℝ ) + 1
                                _
                                by norm_cast simp only [ Nat.succ_ne_zero , not_false_iff ]
                            ,
                            rpow_neg_one k
                            ,
                            sub_eq_add_neg
                          ]
                  · simp only [ add_zero , add_right_neg ]
          refine' squeeze_zero_norm _ H
          intro k
          let U := u k
          let b ( i : ℕ ) x := - ( 1 : ℝ ) ^ i * x ^ 2 * i + 1 / 2 * i + 1
          let f x := arctan x - ∑ i in Finset.range k , b i x
          suffices f_bound : | f 1 - f 0 | ≤ ( 1 : ℝ ) - U + U ^ 2 * ( k : ℝ ) + 1
          · rw [ ← norm_neg ] convert f_bound simp only [ f ] simp [ b ]
          have
            hU1
              : ( U : ℝ ) ≤ 1
              :=
              by
                by_cases hk : k = 0
                  · simp [ u , U , hk ]
                  ·
                    exact
                      rpow_le_one_of_one_le_of_nonpos
                        by norm_cast exact nat.succ_le_iff.mpr Nat.pos_of_ne_zero hk
                          le_of_lt
                            @ div_neg_of_neg_of_pos
                              _
                                _
                                - ( 1 : ℝ )
                                2 * k + 1
                                neg_neg_iff_pos.mpr zero_lt_one
                                by norm_cast exact Nat.succ_pos'
          have hU2 := Nnreal.coe_nonneg U
          let f' := fun x : ℝ => - x ^ 2 ^ k / 1 + x ^ 2
          have
            has_deriv_at_f
              : ∀ x , HasDerivAt f f' x x
              :=
              by
                intro x
                  have
                    has_deriv_at_b
                      : ∀ i ∈ Finset.range k , HasDerivAt b i - x ^ 2 ^ i x
                      :=
                      by
                        intro i hi
                          convert
                            HasDerivAt.const_mul
                              ( - 1 : ℝ ) ^ i / 2 * i + 1
                                @ HasDerivAt.pow _ _ _ _ _ 2 * i + 1 has_deriv_at_id x
                          · ext y simp only [ b , id.def ] ring
                          ·
                            simp
                                only
                                [
                                  Nat.add_succ_sub_one
                                    ,
                                    add_zero
                                    ,
                                    mul_one
                                    ,
                                    id.def
                                    ,
                                    Nat.cast_bit0
                                    ,
                                    Nat.cast_add
                                    ,
                                    Nat.cast_one
                                    ,
                                    Nat.cast_mul
                                  ]
                              rw
                                [
                                  ← mul_assoc
                                    ,
                                    @ div_mul_cancel _ _ 2 * ( i : ℝ ) + 1 _ by norm_cast linarith
                                    ,
                                    pow_mul x 2 i
                                    ,
                                    ← mul_pow - 1 x ^ 2 i
                                  ]
                              ring_nf
                  convert has_deriv_at_arctan x . sub HasDerivAt.sum has_deriv_at_b
                  have
                    g_sum
                      :=
                      @ geom_sum_eq
                        _ _ - x ^ 2 neg_nonpos.mpr sq_nonneg x . trans_lt zero_lt_one . Ne k
                  simp only [ f' ] at g_sum ⊢
                  rw
                    [
                      g_sum
                        ,
                        ← neg_add' x ^ 2 1
                        ,
                        add_comm x ^ 2 1
                        ,
                        sub_eq_add_neg
                        ,
                        neg_div'
                        ,
                        neg_div_neg_eq
                      ]
                  ring
          have
            hderiv1
              : ∀ x ∈ Icc ( U : ℝ ) 1 , HasDerivWithinAt f f' x Icc ( U : ℝ ) 1 x
              :=
              fun x hx => has_deriv_at_f x . HasDerivWithinAt
          have
            hderiv2
              : ∀ x ∈ Icc 0 ( U : ℝ ) , HasDerivWithinAt f f' x Icc 0 ( U : ℝ ) x
              :=
              fun x hx => has_deriv_at_f x . HasDerivWithinAt
          have
            f'_bound
              : ∀ x ∈ Icc ( - 1 : ℝ ) 1 , | f' x | ≤ | x | ^ 2 * k
              :=
              by
                intro x hx
                  rw
                    [
                      abs_div
                        ,
                        IsAbsoluteValue.abv_pow abs - x ^ 2 k
                        ,
                        abs_neg
                        ,
                        IsAbsoluteValue.abv_pow abs x 2
                        ,
                        ← pow_mul
                      ]
                  refine' div_le_of_nonneg_of_le_mul abs_nonneg _ pow_nonneg abs_nonneg _ _ _
                  refine' le_mul_of_one_le_right pow_nonneg abs_nonneg _ _ _
                  rw [ abs_of_nonneg ( add_nonneg zero_le_one sq_nonneg x : ( 0 : ℝ ) ≤ _ ) ]
                  exact ( le_add_of_nonneg_right sq_nonneg x : ( 1 : ℝ ) ≤ _ )
          have
            hbound1
              : ∀ x ∈ Ico ( U : ℝ ) 1 , | f' x | ≤ 1
              :=
              by
                rintro x ⟨ hx_left , hx_right ⟩
                  have hincr := pow_le_pow_of_le_left le_trans hU2 hx_left le_of_lt hx_right 2 * k
                  rw [ one_pow 2 * k , ← abs_of_nonneg le_trans hU2 hx_left ] at hincr
                  rw [ ← abs_of_nonneg le_trans hU2 hx_left ] at hx_right
                  linarith [ f'_bound x mem_Icc.mpr abs_le.mp le_of_lt hx_right ]
          have
            hbound2
              : ∀ x ∈ Ico 0 ( U : ℝ ) , | f' x | ≤ U ^ 2 * k
              :=
              by
                rintro x ⟨ hx_left , hx_right ⟩
                  have hincr := pow_le_pow_of_le_left hx_left le_of_lt hx_right 2 * k
                  rw [ ← abs_of_nonneg hx_left ] at hincr hx_right
                  rw [ ← abs_of_nonneg hU2 ] at hU1 hx_right
                  linarith [ f'_bound x mem_Icc.mpr abs_le.mp le_trans le_of_lt hx_right hU1 ]
          have
            mvt1
              :=
              norm_image_sub_le_of_norm_deriv_le_segment' hderiv1 hbound1 _ right_mem_Icc.mpr hU1
          have
            mvt2
              :=
              norm_image_sub_le_of_norm_deriv_le_segment' hderiv2 hbound2 _ right_mem_Icc.mpr hU2
          calc
            | f 1 - f 0 | = | f 1 - f U + f U - f 0 | := by ring_nf
            _ ≤ 1 * 1 - U + U ^ 2 * k * U - 0
                :=
                le_trans abs_add f 1 - f U f U - f 0 add_le_add mvt1 mvt2
              _ = 1 - U + U ^ 2 * k * U := by ring
              _ = 1 - u k + u k ^ 2 * ( k : ℝ ) + 1
                :=
                by rw [ ← pow_succ' ( U : ℝ ) 2 * k ] norm_cast
#align real.tendsto_sum_pi_div_four Real.tendsto_sum_pi_div_four

end Real

