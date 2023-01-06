/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module analysis.hofer
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecificLimits.Basic

/-!
# Hofer's lemma

This is an elementary lemma about complete metric spaces. It is motivated by an
application to the bubbling-off analysis for holomorphic curves in symplectic topology.
We are *very* far away from having these applications, but the proof here is a nice
example of a proof needing to construct a sequence by induction in the middle of the proof.

## References:

* H. Hofer and C. Viterbo, *The Weinstein conjecture in the presence of holomorphic spheres*
-/


open Classical TopologicalSpace BigOperators

open Filter Finset

-- mathport name: exprd
local notation "d" => dist

@[simp]
theorem pos_div_pow_pos {α : Type _} [LinearOrderedSemifield α] {a b : α} (ha : 0 < a) (hb : 0 < b)
    (k : ℕ) : 0 < a / b ^ k :=
  div_pos ha (pow_pos hb k)
#align pos_div_pow_pos pos_div_pow_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `hofer [])
      (Command.declSig
       [(Term.implicitBinder "{" [`X] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`X]) "]")
        (Term.instBinder "[" [] (Term.app `CompleteSpace [`X]) "]")
        (Term.explicitBinder "(" [`x] [":" `X] [] ")")
        (Term.explicitBinder "(" [`ε] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")
        (Term.explicitBinder "(" [`ε_pos] [":" («term_<_» (num "0") "<" `ε)] [] ")")
        (Term.implicitBinder "{" [`ϕ] [":" (Term.arrow `X "→" (Data.Real.Basic.termℝ "ℝ"))] "}")
        (Term.explicitBinder "(" [`cont] [":" (Term.app `Continuous [`ϕ])] [] ")")
        (Term.explicitBinder
         "("
         [`nonneg]
         [":" (Term.forall "∀" [`y] [] "," («term_≤_» (num "0") "≤" (Term.app `ϕ [`y])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Std.ExtendedBinder.«term∃__,_»
         "∃"
         (Lean.binderIdent `ε')
         (Std.ExtendedBinder.«binderTerm>_» ">" (num "0"))
         ","
         («term∃_,_»
          "∃"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x')] [":" `X]))
          ","
          («term_∧_»
           («term_≤_» `ε' "≤" `ε)
           "∧"
           («term_∧_»
            («term_≤_»
             (Term.app (Analysis.Hofer.termd "d") [`x' `x])
             "≤"
             («term_*_» (num "2") "*" `ε))
            "∧"
            («term_∧_»
             («term_≤_»
              («term_*_» `ε "*" (Term.app `ϕ [`x]))
              "≤"
              («term_*_» `ε' "*" (Term.app `ϕ [`x'])))
             "∧"
             (Term.forall
              "∀"
              [`y]
              []
              ","
              (Term.arrow
               («term_≤_» (Term.app (Analysis.Hofer.termd "d") [`x' `y]) "≤" `ε')
               "→"
               («term_≤_»
                (Term.app `ϕ [`y])
                "≤"
                («term_*_» (num "2") "*" (Term.app `ϕ [`x']))))))))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.byContra "by_contra" [(Lean.binderIdent `H)])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`reformulation []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [(Term.explicitBinder "(" [`x'] [] [] ")")
                  (Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")]
                 []
                 ","
                 («term_↔_»
                  («term_≤_»
                   («term_*_» `ε "*" (Term.app `ϕ [`x]))
                   "≤"
                   («term_*_»
                    («term_/_» `ε "/" («term_^_» (num "2") "^" `k))
                    "*"
                    (Term.app `ϕ [`x'])))
                  "↔"
                  («term_≤_»
                   («term_*_» («term_^_» (num "2") "^" `k) "*" (Term.app `ϕ [`x]))
                   "≤"
                   (Term.app `ϕ [`x'])))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`x' `k])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `div_mul_eq_mul_div)
                     ","
                     (Tactic.rwRule [] `le_div_iff)
                     ","
                     (Tactic.rwRule [] `mul_assoc)
                     ","
                     (Tactic.rwRule [] (Term.app `mul_le_mul_left [`ε_pos]))
                     ","
                     (Tactic.rwRule [] `mul_comm)]
                    "]")
                   [])
                  []
                  (Mathlib.Tactic.Positivity.positivity "positivity")]))))))
           []
           (Mathlib.Tactic.replace'
            "replace"
            [`H []]
            [(Term.typeSpec
              ":"
              (Term.forall
               "∀"
               [`k]
               [(Term.typeSpec ":" (termℕ "ℕ"))]
               ","
               (Term.forall
                "∀"
                [`x']
                []
                ","
                (Term.arrow
                 («term_∧_»
                  («term_≤_»
                   (Term.app (Analysis.Hofer.termd "d") [`x' `x])
                   "≤"
                   («term_*_» (num "2") "*" `ε))
                  "∧"
                  («term_≤_»
                   («term_*_» («term_^_» (num "2") "^" `k) "*" (Term.app `ϕ [`x]))
                   "≤"
                   (Term.app `ϕ [`x'])))
                 "→"
                 («term∃_,_»
                  "∃"
                  (Lean.explicitBinders
                   (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
                  ","
                  («term_∧_»
                   («term_≤_»
                    (Term.app (Analysis.Hofer.termd "d") [`x' `y])
                    "≤"
                    («term_/_» `ε "/" («term_^_» (num "2") "^" `k)))
                   "∧"
                   («term_<_»
                    («term_*_» (num "2") "*" (Term.app `ϕ [`x']))
                    "<"
                    (Term.app `ϕ [`y]))))))))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`k `x'])
             []
             (Mathlib.Tactic.PushNeg.tacticPush_neg__
              "push_neg"
              [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `reformulation)] "]")]
               ["using"
                (Term.app
                 `H
                 [(«term_/_» `ε "/" («term_^_» (num "2") "^" `k))
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       []
                       ["[" [(Tactic.simpLemma [] [] `ε_pos)] "]"]
                       [])])))
                  `x'
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       []
                       ["["
                        [(Tactic.simpLemma [] [] `ε_pos.le)
                         ","
                         (Tactic.simpLemma [] [] `one_le_two)]
                        "]"]
                       [])])))])]))])
           []
           (Tactic.clear "clear" [`reformulation])
           []
           (Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" (Term.app `Nonempty [`X]))]
              ":="
              (Term.anonymousCtor "⟨" [`x] "⟩"))))
           []
           (Mathlib.Tactic.Choose.tacticChoose!__Using_
            "choose!"
            [(Lean.binderIdent `F) (Lean.binderIdent `hF)]
            ["using" `H])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `u
              []
              [(Term.typeSpec ":" (Term.arrow (termℕ "ℕ") "→" `X))]
              ":="
              (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.app `Nat.recOn [`n `x `F]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hu0 []]
              [(Term.typeSpec ":" («term_=_» (Term.app `u [(num "0")]) "=" `x))]
              ":="
              `rfl)))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hu []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`n]
                 []
                 ","
                 (Term.arrow
                  («term_∧_»
                   («term_≤_»
                    (Term.app (Analysis.Hofer.termd "d") [(Term.app `u [`n]) `x])
                    "≤"
                    («term_*_» (num "2") "*" `ε))
                   "∧"
                   («term_≤_»
                    («term_*_» («term_^_» (num "2") "^" `n) "*" (Term.app `ϕ [`x]))
                    "≤"
                    (Term.app `ϕ [(Term.app `u [`n])])))
                  "→"
                  («term_∧_»
                   («term_≤_»
                    (Term.app
                     (Analysis.Hofer.termd "d")
                     [(Term.app `u [`n]) («term_<|_» `u "<|" («term_+_» `n "+" (num "1")))])
                    "≤"
                    («term_/_» `ε "/" («term_^_» (num "2") "^" `n)))
                   "∧"
                   («term_<_»
                    («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [`n])]))
                    "<"
                    (Term.app `ϕ [(«term_<|_» `u "<|" («term_+_» `n "+" (num "1")))]))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`n])
                  []
                  (Tactic.exact "exact" (Term.app `hF [`n (Term.app `u [`n])]))]))))))
           []
           (Tactic.clear "clear" [`hF])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`key []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`n]
                 []
                 ","
                 («term_∧_»
                  («term_≤_»
                   (Term.app
                    (Analysis.Hofer.termd "d")
                    [(Term.app `u [`n]) (Term.app `u [(«term_+_» `n "+" (num "1"))])])
                   "≤"
                   («term_/_» `ε "/" («term_^_» (num "2") "^" `n)))
                  "∧"
                  («term_<_»
                   («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [`n])]))
                   "<"
                   (Term.app `ϕ [(Term.app `u [(«term_+_» `n "+" (num "1"))])])))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`n])
                  []
                  (Tactic.induction'
                   "induction'"
                   [(Tactic.casesTarget [] `n)]
                   ["using" `Nat.case_strong_induction_on]
                   ["with" [(Lean.binderIdent `n) (Lean.binderIdent `IH)]]
                   [])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.specialize "specialize" (Term.app `hu [(num "0")]))
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
                        [(Tactic.simpLemma [] [] `hu0)
                         ","
                         (Tactic.simpLemma [] [] `mul_nonneg_iff)
                         ","
                         (Tactic.simpLemma [] [] `zero_le_one)
                         ","
                         (Tactic.simpLemma [] [] `ε_pos.le)
                         ","
                         (Tactic.simpLemma [] [] `le_refl)]
                        "]")]
                      ["using" `hu]))])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`A []]
                     [(Term.typeSpec
                       ":"
                       («term_≤_»
                        (Term.app
                         (Analysis.Hofer.termd "d")
                         [(Term.app `u [(«term_+_» `n "+" (num "1"))]) `x])
                        "≤"
                        («term_*_» (num "2") "*" `ε)))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_comm)] "]")
                          [])
                         []
                         (Tactic.tacticLet_
                          "let"
                          (Term.letDecl
                           (Term.letIdDecl
                            `r
                            []
                            []
                            ":="
                            (Term.app `range [(«term_+_» `n "+" (num "1"))]))))
                         []
                         (calcTactic
                          "calc"
                          (calcStep
                           («term_≤_»
                            (Term.app
                             (Analysis.Hofer.termd "d")
                             [(Term.app `u [(num "0")])
                              (Term.app `u [(«term_+_» `n "+" (num "1"))])])
                            "≤"
                            (BigOperators.Algebra.BigOperators.Basic.finset.sum
                             "∑"
                             (Std.ExtendedBinder.extBinders
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                             " in "
                             `r
                             ", "
                             (Term.app
                              (Analysis.Hofer.termd "d")
                              [(Term.app `u [`i])
                               («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))])))
                           ":="
                           (Term.app `dist_le_range_sum_dist [`u («term_+_» `n "+" (num "1"))]))
                          [(calcStep
                            («term_≤_»
                             (Term.hole "_")
                             "≤"
                             (BigOperators.Algebra.BigOperators.Basic.finset.sum
                              "∑"
                              (Std.ExtendedBinder.extBinders
                               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                              " in "
                              `r
                              ", "
                              («term_/_» `ε "/" («term_^_» (num "2") "^" `i))))
                            ":="
                            (Term.app
                             `sum_le_sum
                             [(Term.fun
                               "fun"
                               (Term.basicFun
                                [`i `i_in]
                                []
                                "=>"
                                (Term.proj
                                 («term_<|_»
                                  (Term.app `IH [`i])
                                  "<|"
                                  («term_<|_»
                                   `nat.lt_succ_iff.mp
                                   "<|"
                                   (Term.app `finset.mem_range.mp [`i_in])))
                                 "."
                                 (fieldIdx "1"))))]))
                           (calcStep
                            («term_=_»
                             (Term.hole "_")
                             "="
                             (BigOperators.Algebra.BigOperators.Basic.finset.sum
                              "∑"
                              (Std.ExtendedBinder.extBinders
                               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                              " in "
                              `r
                              ", "
                              («term_*_»
                               («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i)
                               "*"
                               `ε)))
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Std.Tactic.congrWith
                                 "congr"
                                 []
                                 "with"
                                 [(Std.Tactic.RCases.rintroPat.one
                                   (Std.Tactic.RCases.rcasesPat.one `i))]
                                 [])
                                []
                                (Tactic.fieldSimp "field_simp" [] [] [] [] [])]))))
                           (calcStep
                            («term_=_»
                             (Term.hole "_")
                             "="
                             («term_*_»
                              (BigOperators.Algebra.BigOperators.Basic.finset.sum
                               "∑"
                               (Std.ExtendedBinder.extBinders
                                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                               " in "
                               `r
                               ", "
                               («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i))
                              "*"
                              `ε))
                            ":="
                            `finset.sum_mul.symm)
                           (calcStep
                            («term_≤_» (Term.hole "_") "≤" («term_*_» (num "2") "*" `ε))
                            ":="
                            (Term.app
                             `mul_le_mul_of_nonneg_right
                             [(Term.app `sum_geometric_two_le [(Term.hole "_")])
                              (Term.app `le_of_lt [`ε_pos])]))])]))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`B []]
                     [(Term.typeSpec
                       ":"
                       («term_≤_»
                        («term_*_»
                         («term_^_» (num "2") "^" («term_+_» `n "+" (num "1")))
                         "*"
                         (Term.app `ϕ [`x]))
                        "≤"
                        (Term.app `ϕ [(Term.app `u [(«term_+_» `n "+" (num "1"))])])))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.refine'
                          "refine'"
                          (Term.app
                           (Term.explicit "@" `geom_le)
                           [(«term_∘_» `ϕ "∘" `u)
                            (Term.hole "_")
                            `zero_le_two
                            («term_+_» `n "+" (num "1"))
                            (Term.fun "fun" (Term.basicFun [`m `hm] [] "=>" (Term.hole "_")))]))
                         []
                         (Tactic.exact
                          "exact"
                          (Term.proj
                           (Term.proj
                            («term_<|_»
                             (Term.app `IH [(Term.hole "_")])
                             "<|"
                             (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm]))
                            "."
                            (fieldIdx "2"))
                           "."
                           `le))]))))))
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `hu
                    [(«term_+_» `n "+" (num "1")) (Term.anonymousCtor "⟨" [`A "," `B] "⟩")]))]))))))
           []
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] (Term.app `forall_and_distrib.mp [`key]))]
            []
            ["with" [(Lean.binderIdent `key₁) (Lean.binderIdent `key₂)]])
           []
           (Tactic.clear "clear" [`hu `key])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`cauchy_u []]
              [(Term.typeSpec ":" (Term.app `CauchySeq [`u]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.refine'
                   "refine'"
                   (Term.app
                    `cauchy_seq_of_le_geometric
                    [(Term.hole "_")
                     `ε
                     `one_half_lt_one
                     (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))]))
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
                      [(Tactic.simpLemma [] [] `one_div) "," (Tactic.simpLemma [] [] `inv_pow)]
                      "]")]
                    ["using" (Term.app `key₁ [`n])]))]))))))
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `limy)])
                  [])]
                "⟩")])]
            [":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
              ","
              (Term.app
               `tendsto
               [`u `at_top (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y])]))]
            [])
           []
           (Tactic.exact "exact" (Term.app `CompleteSpace.complete [`cauchy_u]))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`lim_top []]
              [(Term.typeSpec ":" (Term.app `tendsto [(«term_∘_» `ϕ "∘" `u) `at_top `at_top]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `v
                     [`n]
                     []
                     ":="
                     (Term.app («term_∘_» `ϕ "∘" `u) [(«term_+_» `n "+" (num "1"))]))))
                  []
                  (Tactic.tacticSuffices_
                   "suffices"
                   (Term.sufficesDecl
                    []
                    (Term.app `tendsto [`v `at_top `at_top])
                    (Term.byTactic'
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Std.Tactic.tacticRwa__
                         "rwa"
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_add_at_top_iff_nat)] "]")
                         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hv₀ []]
                     [(Term.typeSpec ":" («term_<_» (num "0") "<" (Term.app `v [(num "0")])))]
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
                              («term_≤_» (num "0") "≤" (Term.app `ϕ [(Term.app `u [(num "0")])])))]
                            ":="
                            (Term.app `nonneg [`x]))))
                         []
                         (calcTactic
                          "calc"
                          (calcStep
                           («term_≤_»
                            (num "0")
                            "≤"
                            («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [(num "0")])])))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))
                          [(calcStep
                            («term_<_»
                             (Term.hole "_")
                             "<"
                             (Term.app `ϕ [(Term.app `u [(«term_+_» (num "0") "+" (num "1"))])]))
                            ":="
                            (Term.app `key₂ [(num "0")]))])]))))))
                  []
                  (Tactic.apply "apply" (Term.app `tendsto_at_top_of_geom_le [`hv₀ `one_lt_two]))
                  []
                  (Tactic.exact
                   "exact"
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`n]
                     []
                     "=>"
                     (Term.proj (Term.app `key₂ [(«term_+_» `n "+" (num "1"))]) "." `le))))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`lim []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `tendsto
                 [(«term_∘_» `ϕ "∘" `u)
                  `at_top
                  (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.app `ϕ [`y])])]))]
              ":="
              (Term.app `tendsto.comp [`cont.continuous_at `limy]))))
           []
           (Tactic.exact "exact" (Term.app `not_tendsto_at_top_of_tendsto_nhds [`lim `lim_top]))])))
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
         [(Std.Tactic.byContra "by_contra" [(Lean.binderIdent `H)])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`reformulation []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [(Term.explicitBinder "(" [`x'] [] [] ")")
                 (Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")]
                []
                ","
                («term_↔_»
                 («term_≤_»
                  («term_*_» `ε "*" (Term.app `ϕ [`x]))
                  "≤"
                  («term_*_»
                   («term_/_» `ε "/" («term_^_» (num "2") "^" `k))
                   "*"
                   (Term.app `ϕ [`x'])))
                 "↔"
                 («term_≤_»
                  («term_*_» («term_^_» (num "2") "^" `k) "*" (Term.app `ϕ [`x]))
                  "≤"
                  (Term.app `ϕ [`x'])))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`x' `k])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `div_mul_eq_mul_div)
                    ","
                    (Tactic.rwRule [] `le_div_iff)
                    ","
                    (Tactic.rwRule [] `mul_assoc)
                    ","
                    (Tactic.rwRule [] (Term.app `mul_le_mul_left [`ε_pos]))
                    ","
                    (Tactic.rwRule [] `mul_comm)]
                   "]")
                  [])
                 []
                 (Mathlib.Tactic.Positivity.positivity "positivity")]))))))
          []
          (Mathlib.Tactic.replace'
           "replace"
           [`H []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`k]
              [(Term.typeSpec ":" (termℕ "ℕ"))]
              ","
              (Term.forall
               "∀"
               [`x']
               []
               ","
               (Term.arrow
                («term_∧_»
                 («term_≤_»
                  (Term.app (Analysis.Hofer.termd "d") [`x' `x])
                  "≤"
                  («term_*_» (num "2") "*" `ε))
                 "∧"
                 («term_≤_»
                  («term_*_» («term_^_» (num "2") "^" `k) "*" (Term.app `ϕ [`x]))
                  "≤"
                  (Term.app `ϕ [`x'])))
                "→"
                («term∃_,_»
                 "∃"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
                 ","
                 («term_∧_»
                  («term_≤_»
                   (Term.app (Analysis.Hofer.termd "d") [`x' `y])
                   "≤"
                   («term_/_» `ε "/" («term_^_» (num "2") "^" `k)))
                  "∧"
                  («term_<_»
                   («term_*_» (num "2") "*" (Term.app `ϕ [`x']))
                   "<"
                   (Term.app `ϕ [`y]))))))))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`k `x'])
            []
            (Mathlib.Tactic.PushNeg.tacticPush_neg__
             "push_neg"
             [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
            []
            (Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `reformulation)] "]")]
              ["using"
               (Term.app
                `H
                [(«term_/_» `ε "/" («term_^_» (num "2") "^" `k))
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["[" [(Tactic.simpLemma [] [] `ε_pos)] "]"]
                      [])])))
                 `x'
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["["
                       [(Tactic.simpLemma [] [] `ε_pos.le) "," (Tactic.simpLemma [] [] `one_le_two)]
                       "]"]
                      [])])))])]))])
          []
          (Tactic.clear "clear" [`reformulation])
          []
          (Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `Nonempty [`X]))]
             ":="
             (Term.anonymousCtor "⟨" [`x] "⟩"))))
          []
          (Mathlib.Tactic.Choose.tacticChoose!__Using_
           "choose!"
           [(Lean.binderIdent `F) (Lean.binderIdent `hF)]
           ["using" `H])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `u
             []
             [(Term.typeSpec ":" (Term.arrow (termℕ "ℕ") "→" `X))]
             ":="
             (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.app `Nat.recOn [`n `x `F]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hu0 []]
             [(Term.typeSpec ":" («term_=_» (Term.app `u [(num "0")]) "=" `x))]
             ":="
             `rfl)))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hu []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`n]
                []
                ","
                (Term.arrow
                 («term_∧_»
                  («term_≤_»
                   (Term.app (Analysis.Hofer.termd "d") [(Term.app `u [`n]) `x])
                   "≤"
                   («term_*_» (num "2") "*" `ε))
                  "∧"
                  («term_≤_»
                   («term_*_» («term_^_» (num "2") "^" `n) "*" (Term.app `ϕ [`x]))
                   "≤"
                   (Term.app `ϕ [(Term.app `u [`n])])))
                 "→"
                 («term_∧_»
                  («term_≤_»
                   (Term.app
                    (Analysis.Hofer.termd "d")
                    [(Term.app `u [`n]) («term_<|_» `u "<|" («term_+_» `n "+" (num "1")))])
                   "≤"
                   («term_/_» `ε "/" («term_^_» (num "2") "^" `n)))
                  "∧"
                  («term_<_»
                   («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [`n])]))
                   "<"
                   (Term.app `ϕ [(«term_<|_» `u "<|" («term_+_» `n "+" (num "1")))]))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`n])
                 []
                 (Tactic.exact "exact" (Term.app `hF [`n (Term.app `u [`n])]))]))))))
          []
          (Tactic.clear "clear" [`hF])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`key []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`n]
                []
                ","
                («term_∧_»
                 («term_≤_»
                  (Term.app
                   (Analysis.Hofer.termd "d")
                   [(Term.app `u [`n]) (Term.app `u [(«term_+_» `n "+" (num "1"))])])
                  "≤"
                  («term_/_» `ε "/" («term_^_» (num "2") "^" `n)))
                 "∧"
                 («term_<_»
                  («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [`n])]))
                  "<"
                  (Term.app `ϕ [(Term.app `u [(«term_+_» `n "+" (num "1"))])])))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`n])
                 []
                 (Tactic.induction'
                  "induction'"
                  [(Tactic.casesTarget [] `n)]
                  ["using" `Nat.case_strong_induction_on]
                  ["with" [(Lean.binderIdent `n) (Lean.binderIdent `IH)]]
                  [])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.specialize "specialize" (Term.app `hu [(num "0")]))
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
                       [(Tactic.simpLemma [] [] `hu0)
                        ","
                        (Tactic.simpLemma [] [] `mul_nonneg_iff)
                        ","
                        (Tactic.simpLemma [] [] `zero_le_one)
                        ","
                        (Tactic.simpLemma [] [] `ε_pos.le)
                        ","
                        (Tactic.simpLemma [] [] `le_refl)]
                       "]")]
                     ["using" `hu]))])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`A []]
                    [(Term.typeSpec
                      ":"
                      («term_≤_»
                       (Term.app
                        (Analysis.Hofer.termd "d")
                        [(Term.app `u [(«term_+_» `n "+" (num "1"))]) `x])
                       "≤"
                       («term_*_» (num "2") "*" `ε)))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_comm)] "]")
                         [])
                        []
                        (Tactic.tacticLet_
                         "let"
                         (Term.letDecl
                          (Term.letIdDecl
                           `r
                           []
                           []
                           ":="
                           (Term.app `range [(«term_+_» `n "+" (num "1"))]))))
                        []
                        (calcTactic
                         "calc"
                         (calcStep
                          («term_≤_»
                           (Term.app
                            (Analysis.Hofer.termd "d")
                            [(Term.app `u [(num "0")])
                             (Term.app `u [(«term_+_» `n "+" (num "1"))])])
                           "≤"
                           (BigOperators.Algebra.BigOperators.Basic.finset.sum
                            "∑"
                            (Std.ExtendedBinder.extBinders
                             (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                            " in "
                            `r
                            ", "
                            (Term.app
                             (Analysis.Hofer.termd "d")
                             [(Term.app `u [`i])
                              («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))])))
                          ":="
                          (Term.app `dist_le_range_sum_dist [`u («term_+_» `n "+" (num "1"))]))
                         [(calcStep
                           («term_≤_»
                            (Term.hole "_")
                            "≤"
                            (BigOperators.Algebra.BigOperators.Basic.finset.sum
                             "∑"
                             (Std.ExtendedBinder.extBinders
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                             " in "
                             `r
                             ", "
                             («term_/_» `ε "/" («term_^_» (num "2") "^" `i))))
                           ":="
                           (Term.app
                            `sum_le_sum
                            [(Term.fun
                              "fun"
                              (Term.basicFun
                               [`i `i_in]
                               []
                               "=>"
                               (Term.proj
                                («term_<|_»
                                 (Term.app `IH [`i])
                                 "<|"
                                 («term_<|_»
                                  `nat.lt_succ_iff.mp
                                  "<|"
                                  (Term.app `finset.mem_range.mp [`i_in])))
                                "."
                                (fieldIdx "1"))))]))
                          (calcStep
                           («term_=_»
                            (Term.hole "_")
                            "="
                            (BigOperators.Algebra.BigOperators.Basic.finset.sum
                             "∑"
                             (Std.ExtendedBinder.extBinders
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                             " in "
                             `r
                             ", "
                             («term_*_»
                              («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i)
                              "*"
                              `ε)))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Std.Tactic.congrWith
                                "congr"
                                []
                                "with"
                                [(Std.Tactic.RCases.rintroPat.one
                                  (Std.Tactic.RCases.rcasesPat.one `i))]
                                [])
                               []
                               (Tactic.fieldSimp "field_simp" [] [] [] [] [])]))))
                          (calcStep
                           («term_=_»
                            (Term.hole "_")
                            "="
                            («term_*_»
                             (BigOperators.Algebra.BigOperators.Basic.finset.sum
                              "∑"
                              (Std.ExtendedBinder.extBinders
                               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                              " in "
                              `r
                              ", "
                              («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i))
                             "*"
                             `ε))
                           ":="
                           `finset.sum_mul.symm)
                          (calcStep
                           («term_≤_» (Term.hole "_") "≤" («term_*_» (num "2") "*" `ε))
                           ":="
                           (Term.app
                            `mul_le_mul_of_nonneg_right
                            [(Term.app `sum_geometric_two_le [(Term.hole "_")])
                             (Term.app `le_of_lt [`ε_pos])]))])]))))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`B []]
                    [(Term.typeSpec
                      ":"
                      («term_≤_»
                       («term_*_»
                        («term_^_» (num "2") "^" («term_+_» `n "+" (num "1")))
                        "*"
                        (Term.app `ϕ [`x]))
                       "≤"
                       (Term.app `ϕ [(Term.app `u [(«term_+_» `n "+" (num "1"))])])))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.refine'
                         "refine'"
                         (Term.app
                          (Term.explicit "@" `geom_le)
                          [(«term_∘_» `ϕ "∘" `u)
                           (Term.hole "_")
                           `zero_le_two
                           («term_+_» `n "+" (num "1"))
                           (Term.fun "fun" (Term.basicFun [`m `hm] [] "=>" (Term.hole "_")))]))
                        []
                        (Tactic.exact
                         "exact"
                         (Term.proj
                          (Term.proj
                           («term_<|_»
                            (Term.app `IH [(Term.hole "_")])
                            "<|"
                            (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm]))
                           "."
                           (fieldIdx "2"))
                          "."
                          `le))]))))))
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `hu
                   [(«term_+_» `n "+" (num "1")) (Term.anonymousCtor "⟨" [`A "," `B] "⟩")]))]))))))
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] (Term.app `forall_and_distrib.mp [`key]))]
           []
           ["with" [(Lean.binderIdent `key₁) (Lean.binderIdent `key₂)]])
          []
          (Tactic.clear "clear" [`hu `key])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`cauchy_u []]
             [(Term.typeSpec ":" (Term.app `CauchySeq [`u]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine'
                  "refine'"
                  (Term.app
                   `cauchy_seq_of_le_geometric
                   [(Term.hole "_")
                    `ε
                    `one_half_lt_one
                    (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))]))
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
                     [(Tactic.simpLemma [] [] `one_div) "," (Tactic.simpLemma [] [] `inv_pow)]
                     "]")]
                   ["using" (Term.app `key₁ [`n])]))]))))))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `limy)])
                 [])]
               "⟩")])]
           [":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
             ","
             (Term.app
              `tendsto
              [`u `at_top (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y])]))]
           [])
          []
          (Tactic.exact "exact" (Term.app `CompleteSpace.complete [`cauchy_u]))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`lim_top []]
             [(Term.typeSpec ":" (Term.app `tendsto [(«term_∘_» `ϕ "∘" `u) `at_top `at_top]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `v
                    [`n]
                    []
                    ":="
                    (Term.app («term_∘_» `ϕ "∘" `u) [(«term_+_» `n "+" (num "1"))]))))
                 []
                 (Tactic.tacticSuffices_
                  "suffices"
                  (Term.sufficesDecl
                   []
                   (Term.app `tendsto [`v `at_top `at_top])
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Std.Tactic.tacticRwa__
                        "rwa"
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_add_at_top_iff_nat)] "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hv₀ []]
                    [(Term.typeSpec ":" («term_<_» (num "0") "<" (Term.app `v [(num "0")])))]
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
                             («term_≤_» (num "0") "≤" (Term.app `ϕ [(Term.app `u [(num "0")])])))]
                           ":="
                           (Term.app `nonneg [`x]))))
                        []
                        (calcTactic
                         "calc"
                         (calcStep
                          («term_≤_»
                           (num "0")
                           "≤"
                           («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [(num "0")])])))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))
                         [(calcStep
                           («term_<_»
                            (Term.hole "_")
                            "<"
                            (Term.app `ϕ [(Term.app `u [(«term_+_» (num "0") "+" (num "1"))])]))
                           ":="
                           (Term.app `key₂ [(num "0")]))])]))))))
                 []
                 (Tactic.apply "apply" (Term.app `tendsto_at_top_of_geom_le [`hv₀ `one_lt_two]))
                 []
                 (Tactic.exact
                  "exact"
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`n]
                    []
                    "=>"
                    (Term.proj (Term.app `key₂ [(«term_+_» `n "+" (num "1"))]) "." `le))))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`lim []]
             [(Term.typeSpec
               ":"
               (Term.app
                `tendsto
                [(«term_∘_» `ϕ "∘" `u)
                 `at_top
                 (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.app `ϕ [`y])])]))]
             ":="
             (Term.app `tendsto.comp [`cont.continuous_at `limy]))))
          []
          (Tactic.exact "exact" (Term.app `not_tendsto_at_top_of_tendsto_nhds [`lim `lim_top]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `not_tendsto_at_top_of_tendsto_nhds [`lim `lim_top]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not_tendsto_at_top_of_tendsto_nhds [`lim `lim_top])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lim_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `lim
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_tendsto_at_top_of_tendsto_nhds
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`lim []]
         [(Term.typeSpec
           ":"
           (Term.app
            `tendsto
            [(«term_∘_» `ϕ "∘" `u)
             `at_top
             (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.app `ϕ [`y])])]))]
         ":="
         (Term.app `tendsto.comp [`cont.continuous_at `limy]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tendsto.comp [`cont.continuous_at `limy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `limy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cont.continuous_at
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto
       [(«term_∘_» `ϕ "∘" `u)
        `at_top
        (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.app `ϕ [`y])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.app `ϕ [`y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ϕ [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `ϕ [`y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.paren "(" (Term.app `ϕ [`y]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `at_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_∘_» `ϕ "∘" `u)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `ϕ
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_∘_» `ϕ "∘" `u) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`lim_top []]
         [(Term.typeSpec ":" (Term.app `tendsto [(«term_∘_» `ϕ "∘" `u) `at_top `at_top]))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `v
                [`n]
                []
                ":="
                (Term.app («term_∘_» `ϕ "∘" `u) [(«term_+_» `n "+" (num "1"))]))))
             []
             (Tactic.tacticSuffices_
              "suffices"
              (Term.sufficesDecl
               []
               (Term.app `tendsto [`v `at_top `at_top])
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.tacticRwa__
                    "rwa"
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_add_at_top_iff_nat)] "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hv₀ []]
                [(Term.typeSpec ":" («term_<_» (num "0") "<" (Term.app `v [(num "0")])))]
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
                         («term_≤_» (num "0") "≤" (Term.app `ϕ [(Term.app `u [(num "0")])])))]
                       ":="
                       (Term.app `nonneg [`x]))))
                    []
                    (calcTactic
                     "calc"
                     (calcStep
                      («term_≤_»
                       (num "0")
                       "≤"
                       («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [(num "0")])])))
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))
                     [(calcStep
                       («term_<_»
                        (Term.hole "_")
                        "<"
                        (Term.app `ϕ [(Term.app `u [(«term_+_» (num "0") "+" (num "1"))])]))
                       ":="
                       (Term.app `key₂ [(num "0")]))])]))))))
             []
             (Tactic.apply "apply" (Term.app `tendsto_at_top_of_geom_le [`hv₀ `one_lt_two]))
             []
             (Tactic.exact
              "exact"
              (Term.fun
               "fun"
               (Term.basicFun
                [`n]
                []
                "=>"
                (Term.proj (Term.app `key₂ [(«term_+_» `n "+" (num "1"))]) "." `le))))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `v
             [`n]
             []
             ":="
             (Term.app («term_∘_» `ϕ "∘" `u) [(«term_+_» `n "+" (num "1"))]))))
          []
          (Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            (Term.app `tendsto [`v `at_top `at_top])
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.tacticRwa__
                 "rwa"
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_add_at_top_iff_nat)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hv₀ []]
             [(Term.typeSpec ":" («term_<_» (num "0") "<" (Term.app `v [(num "0")])))]
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
                      («term_≤_» (num "0") "≤" (Term.app `ϕ [(Term.app `u [(num "0")])])))]
                    ":="
                    (Term.app `nonneg [`x]))))
                 []
                 (calcTactic
                  "calc"
                  (calcStep
                   («term_≤_»
                    (num "0")
                    "≤"
                    («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [(num "0")])])))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))
                  [(calcStep
                    («term_<_»
                     (Term.hole "_")
                     "<"
                     (Term.app `ϕ [(Term.app `u [(«term_+_» (num "0") "+" (num "1"))])]))
                    ":="
                    (Term.app `key₂ [(num "0")]))])]))))))
          []
          (Tactic.apply "apply" (Term.app `tendsto_at_top_of_geom_le [`hv₀ `one_lt_two]))
          []
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`n]
             []
             "=>"
             (Term.proj (Term.app `key₂ [(«term_+_» `n "+" (num "1"))]) "." `le))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.fun
        "fun"
        (Term.basicFun
         [`n]
         []
         "=>"
         (Term.proj (Term.app `key₂ [(«term_+_» `n "+" (num "1"))]) "." `le))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.proj (Term.app `key₂ [(«term_+_» `n "+" (num "1"))]) "." `le)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `key₂ [(«term_+_» `n "+" (num "1"))]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `key₂ [(«term_+_» `n "+" (num "1"))])
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
      `key₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `key₂ [(Term.paren "(" («term_+_» `n "+" (num "1")) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `tendsto_at_top_of_geom_le [`hv₀ `one_lt_two]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tendsto_at_top_of_geom_le [`hv₀ `one_lt_two])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_lt_two
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hv₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_at_top_of_geom_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hv₀ []]
         [(Term.typeSpec ":" («term_<_» (num "0") "<" (Term.app `v [(num "0")])))]
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
                  («term_≤_» (num "0") "≤" (Term.app `ϕ [(Term.app `u [(num "0")])])))]
                ":="
                (Term.app `nonneg [`x]))))
             []
             (calcTactic
              "calc"
              (calcStep
               («term_≤_»
                (num "0")
                "≤"
                («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [(num "0")])])))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))
              [(calcStep
                («term_<_»
                 (Term.hole "_")
                 "<"
                 (Term.app `ϕ [(Term.app `u [(«term_+_» (num "0") "+" (num "1"))])]))
                ":="
                (Term.app `key₂ [(num "0")]))])]))))))
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
               («term_≤_» (num "0") "≤" (Term.app `ϕ [(Term.app `u [(num "0")])])))]
             ":="
             (Term.app `nonneg [`x]))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             (num "0")
             "≤"
             («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [(num "0")])])))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))
           [(calcStep
             («term_<_»
              (Term.hole "_")
              "<"
              (Term.app `ϕ [(Term.app `u [(«term_+_» (num "0") "+" (num "1"))])]))
             ":="
             (Term.app `key₂ [(num "0")]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (num "0")
         "≤"
         («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [(num "0")])])))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))
       [(calcStep
         («term_<_»
          (Term.hole "_")
          "<"
          (Term.app `ϕ [(Term.app `u [(«term_+_» (num "0") "+" (num "1"))])]))
         ":="
         (Term.app `key₂ [(num "0")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `key₂ [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `key₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.hole "_")
       "<"
       (Term.app `ϕ [(Term.app `u [(«term_+_» (num "0") "+" (num "1"))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ϕ [(Term.app `u [(«term_+_» (num "0") "+" (num "1"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `u [(«term_+_» (num "0") "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (num "0") "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» (num "0") "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `u [(Term.paren "(" («term_+_» (num "0") "+" (num "1")) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(linarith "linarith" [] (linarithArgsRest [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (num "0") "≤" («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [(num "0")])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [(num "0")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ϕ [(Term.app `u [(num "0")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `u [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `u [(num "0")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_≤_» (num "0") "≤" (Term.app `ϕ [(Term.app `u [(num "0")])])))]
         ":="
         (Term.app `nonneg [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nonneg [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (num "0") "≤" (Term.app `ϕ [(Term.app `u [(num "0")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ϕ [(Term.app `u [(num "0")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `u [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `u [(num "0")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (num "0") "<" (Term.app `v [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `v [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        (Term.app `tendsto [`v `at_top `at_top])
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_add_at_top_iff_nat)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_add_at_top_iff_nat)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tendsto_add_at_top_iff_nat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tendsto [`v `at_top `at_top])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `at_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `at_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `v
         [`n]
         []
         ":="
         (Term.app («term_∘_» `ϕ "∘" `u) [(«term_+_» `n "+" (num "1"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app («term_∘_» `ϕ "∘" `u) [(«term_+_» `n "+" (num "1"))])
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
      («term_∘_» `ϕ "∘" `u)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `ϕ
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 90, (some 90, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_∘_» `ϕ "∘" `u) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tendsto [(«term_∘_» `ϕ "∘" `u) `at_top `at_top])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `at_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `at_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_∘_» `ϕ "∘" `u)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `ϕ
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_∘_» `ϕ "∘" `u) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `CompleteSpace.complete [`cauchy_u]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `CompleteSpace.complete [`cauchy_u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cauchy_u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `CompleteSpace.complete
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `limy)])
             [])]
           "⟩")])]
       [":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
         ","
         (Term.app
          `tendsto
          [`u `at_top (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y])]))]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
       ","
       (Term.app `tendsto [`u `at_top (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tendsto [`u `at_top (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `at_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`cauchy_u []]
         [(Term.typeSpec ":" (Term.app `CauchySeq [`u]))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.refine'
              "refine'"
              (Term.app
               `cauchy_seq_of_le_geometric
               [(Term.hole "_")
                `ε
                `one_half_lt_one
                (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))]))
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
                 [(Tactic.simpLemma [] [] `one_div) "," (Tactic.simpLemma [] [] `inv_pow)]
                 "]")]
               ["using" (Term.app `key₁ [`n])]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app
            `cauchy_seq_of_le_geometric
            [(Term.hole "_")
             `ε
             `one_half_lt_one
             (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))]))
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
              [(Tactic.simpLemma [] [] `one_div) "," (Tactic.simpLemma [] [] `inv_pow)]
              "]")]
            ["using" (Term.app `key₁ [`n])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
          [(Tactic.simpLemma [] [] `one_div) "," (Tactic.simpLemma [] [] `inv_pow)]
          "]")]
        ["using" (Term.app `key₁ [`n])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `key₁ [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `key₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inv_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_div
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `cauchy_seq_of_le_geometric
        [(Term.hole "_")
         `ε
         `one_half_lt_one
         (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cauchy_seq_of_le_geometric
       [(Term.hole "_")
        `ε
        `one_half_lt_one
        (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `one_half_lt_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cauchy_seq_of_le_geometric
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `CauchySeq [`u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `CauchySeq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.clear "clear" [`hu `key])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `key
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] (Term.app `forall_and_distrib.mp [`key]))]
       []
       ["with" [(Lean.binderIdent `key₁) (Lean.binderIdent `key₂)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `forall_and_distrib.mp [`key])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `key
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `forall_and_distrib.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`key []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`n]
            []
            ","
            («term_∧_»
             («term_≤_»
              (Term.app
               (Analysis.Hofer.termd "d")
               [(Term.app `u [`n]) (Term.app `u [(«term_+_» `n "+" (num "1"))])])
              "≤"
              («term_/_» `ε "/" («term_^_» (num "2") "^" `n)))
             "∧"
             («term_<_»
              («term_*_» (num "2") "*" (Term.app `ϕ [(Term.app `u [`n])]))
              "<"
              (Term.app `ϕ [(Term.app `u [(«term_+_» `n "+" (num "1"))])])))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`n])
             []
             (Tactic.induction'
              "induction'"
              [(Tactic.casesTarget [] `n)]
              ["using" `Nat.case_strong_induction_on]
              ["with" [(Lean.binderIdent `n) (Lean.binderIdent `IH)]]
              [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.specialize "specialize" (Term.app `hu [(num "0")]))
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
                   [(Tactic.simpLemma [] [] `hu0)
                    ","
                    (Tactic.simpLemma [] [] `mul_nonneg_iff)
                    ","
                    (Tactic.simpLemma [] [] `zero_le_one)
                    ","
                    (Tactic.simpLemma [] [] `ε_pos.le)
                    ","
                    (Tactic.simpLemma [] [] `le_refl)]
                   "]")]
                 ["using" `hu]))])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`A []]
                [(Term.typeSpec
                  ":"
                  («term_≤_»
                   (Term.app
                    (Analysis.Hofer.termd "d")
                    [(Term.app `u [(«term_+_» `n "+" (num "1"))]) `x])
                   "≤"
                   («term_*_» (num "2") "*" `ε)))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_comm)] "]")
                     [])
                    []
                    (Tactic.tacticLet_
                     "let"
                     (Term.letDecl
                      (Term.letIdDecl
                       `r
                       []
                       []
                       ":="
                       (Term.app `range [(«term_+_» `n "+" (num "1"))]))))
                    []
                    (calcTactic
                     "calc"
                     (calcStep
                      («term_≤_»
                       (Term.app
                        (Analysis.Hofer.termd "d")
                        [(Term.app `u [(num "0")]) (Term.app `u [(«term_+_» `n "+" (num "1"))])])
                       "≤"
                       (BigOperators.Algebra.BigOperators.Basic.finset.sum
                        "∑"
                        (Std.ExtendedBinder.extBinders
                         (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                        " in "
                        `r
                        ", "
                        (Term.app
                         (Analysis.Hofer.termd "d")
                         [(Term.app `u [`i]) («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))])))
                      ":="
                      (Term.app `dist_le_range_sum_dist [`u («term_+_» `n "+" (num "1"))]))
                     [(calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (BigOperators.Algebra.BigOperators.Basic.finset.sum
                         "∑"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                         " in "
                         `r
                         ", "
                         («term_/_» `ε "/" («term_^_» (num "2") "^" `i))))
                       ":="
                       (Term.app
                        `sum_le_sum
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [`i `i_in]
                           []
                           "=>"
                           (Term.proj
                            («term_<|_»
                             (Term.app `IH [`i])
                             "<|"
                             («term_<|_»
                              `nat.lt_succ_iff.mp
                              "<|"
                              (Term.app `finset.mem_range.mp [`i_in])))
                            "."
                            (fieldIdx "1"))))]))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (BigOperators.Algebra.BigOperators.Basic.finset.sum
                         "∑"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                         " in "
                         `r
                         ", "
                         («term_*_» («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i) "*" `ε)))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Std.Tactic.congrWith
                            "congr"
                            []
                            "with"
                            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
                            [])
                           []
                           (Tactic.fieldSimp "field_simp" [] [] [] [] [])]))))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        («term_*_»
                         (BigOperators.Algebra.BigOperators.Basic.finset.sum
                          "∑"
                          (Std.ExtendedBinder.extBinders
                           (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                          " in "
                          `r
                          ", "
                          («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i))
                         "*"
                         `ε))
                       ":="
                       `finset.sum_mul.symm)
                      (calcStep
                       («term_≤_» (Term.hole "_") "≤" («term_*_» (num "2") "*" `ε))
                       ":="
                       (Term.app
                        `mul_le_mul_of_nonneg_right
                        [(Term.app `sum_geometric_two_le [(Term.hole "_")])
                         (Term.app `le_of_lt [`ε_pos])]))])]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`B []]
                [(Term.typeSpec
                  ":"
                  («term_≤_»
                   («term_*_»
                    («term_^_» (num "2") "^" («term_+_» `n "+" (num "1")))
                    "*"
                    (Term.app `ϕ [`x]))
                   "≤"
                   (Term.app `ϕ [(Term.app `u [(«term_+_» `n "+" (num "1"))])])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.refine'
                     "refine'"
                     (Term.app
                      (Term.explicit "@" `geom_le)
                      [(«term_∘_» `ϕ "∘" `u)
                       (Term.hole "_")
                       `zero_le_two
                       («term_+_» `n "+" (num "1"))
                       (Term.fun "fun" (Term.basicFun [`m `hm] [] "=>" (Term.hole "_")))]))
                    []
                    (Tactic.exact
                     "exact"
                     (Term.proj
                      (Term.proj
                       («term_<|_»
                        (Term.app `IH [(Term.hole "_")])
                        "<|"
                        (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm]))
                       "."
                       (fieldIdx "2"))
                      "."
                      `le))]))))))
             []
             (Tactic.exact
              "exact"
              (Term.app
               `hu
               [(«term_+_» `n "+" (num "1")) (Term.anonymousCtor "⟨" [`A "," `B] "⟩")]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`n])
          []
          (Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `n)]
           ["using" `Nat.case_strong_induction_on]
           ["with" [(Lean.binderIdent `n) (Lean.binderIdent `IH)]]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.specialize "specialize" (Term.app `hu [(num "0")]))
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
                [(Tactic.simpLemma [] [] `hu0)
                 ","
                 (Tactic.simpLemma [] [] `mul_nonneg_iff)
                 ","
                 (Tactic.simpLemma [] [] `zero_le_one)
                 ","
                 (Tactic.simpLemma [] [] `ε_pos.le)
                 ","
                 (Tactic.simpLemma [] [] `le_refl)]
                "]")]
              ["using" `hu]))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`A []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                (Term.app
                 (Analysis.Hofer.termd "d")
                 [(Term.app `u [(«term_+_» `n "+" (num "1"))]) `x])
                "≤"
                («term_*_» (num "2") "*" `ε)))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_comm)] "]")
                  [])
                 []
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl `r [] [] ":=" (Term.app `range [(«term_+_» `n "+" (num "1"))]))))
                 []
                 (calcTactic
                  "calc"
                  (calcStep
                   («term_≤_»
                    (Term.app
                     (Analysis.Hofer.termd "d")
                     [(Term.app `u [(num "0")]) (Term.app `u [(«term_+_» `n "+" (num "1"))])])
                    "≤"
                    (BigOperators.Algebra.BigOperators.Basic.finset.sum
                     "∑"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     " in "
                     `r
                     ", "
                     (Term.app
                      (Analysis.Hofer.termd "d")
                      [(Term.app `u [`i]) («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))])))
                   ":="
                   (Term.app `dist_le_range_sum_dist [`u («term_+_» `n "+" (num "1"))]))
                  [(calcStep
                    («term_≤_»
                     (Term.hole "_")
                     "≤"
                     (BigOperators.Algebra.BigOperators.Basic.finset.sum
                      "∑"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                      " in "
                      `r
                      ", "
                      («term_/_» `ε "/" («term_^_» (num "2") "^" `i))))
                    ":="
                    (Term.app
                     `sum_le_sum
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`i `i_in]
                        []
                        "=>"
                        (Term.proj
                         («term_<|_»
                          (Term.app `IH [`i])
                          "<|"
                          («term_<|_»
                           `nat.lt_succ_iff.mp
                           "<|"
                           (Term.app `finset.mem_range.mp [`i_in])))
                         "."
                         (fieldIdx "1"))))]))
                   (calcStep
                    («term_=_»
                     (Term.hole "_")
                     "="
                     (BigOperators.Algebra.BigOperators.Basic.finset.sum
                      "∑"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                      " in "
                      `r
                      ", "
                      («term_*_» («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i) "*" `ε)))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Std.Tactic.congrWith
                         "congr"
                         []
                         "with"
                         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
                         [])
                        []
                        (Tactic.fieldSimp "field_simp" [] [] [] [] [])]))))
                   (calcStep
                    («term_=_»
                     (Term.hole "_")
                     "="
                     («term_*_»
                      (BigOperators.Algebra.BigOperators.Basic.finset.sum
                       "∑"
                       (Std.ExtendedBinder.extBinders
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                       " in "
                       `r
                       ", "
                       («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i))
                      "*"
                      `ε))
                    ":="
                    `finset.sum_mul.symm)
                   (calcStep
                    («term_≤_» (Term.hole "_") "≤" («term_*_» (num "2") "*" `ε))
                    ":="
                    (Term.app
                     `mul_le_mul_of_nonneg_right
                     [(Term.app `sum_geometric_two_le [(Term.hole "_")])
                      (Term.app `le_of_lt [`ε_pos])]))])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`B []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                («term_*_»
                 («term_^_» (num "2") "^" («term_+_» `n "+" (num "1")))
                 "*"
                 (Term.app `ϕ [`x]))
                "≤"
                (Term.app `ϕ [(Term.app `u [(«term_+_» `n "+" (num "1"))])])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine'
                  "refine'"
                  (Term.app
                   (Term.explicit "@" `geom_le)
                   [(«term_∘_» `ϕ "∘" `u)
                    (Term.hole "_")
                    `zero_le_two
                    («term_+_» `n "+" (num "1"))
                    (Term.fun "fun" (Term.basicFun [`m `hm] [] "=>" (Term.hole "_")))]))
                 []
                 (Tactic.exact
                  "exact"
                  (Term.proj
                   (Term.proj
                    («term_<|_»
                     (Term.app `IH [(Term.hole "_")])
                     "<|"
                     (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm]))
                    "."
                    (fieldIdx "2"))
                   "."
                   `le))]))))))
          []
          (Tactic.exact
           "exact"
           (Term.app
            `hu
            [(«term_+_» `n "+" (num "1")) (Term.anonymousCtor "⟨" [`A "," `B] "⟩")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `hu [(«term_+_» `n "+" (num "1")) (Term.anonymousCtor "⟨" [`A "," `B] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hu [(«term_+_» `n "+" (num "1")) (Term.anonymousCtor "⟨" [`A "," `B] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`A "," `B] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`B []]
         [(Term.typeSpec
           ":"
           («term_≤_»
            («term_*_»
             («term_^_» (num "2") "^" («term_+_» `n "+" (num "1")))
             "*"
             (Term.app `ϕ [`x]))
            "≤"
            (Term.app `ϕ [(Term.app `u [(«term_+_» `n "+" (num "1"))])])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.refine'
              "refine'"
              (Term.app
               (Term.explicit "@" `geom_le)
               [(«term_∘_» `ϕ "∘" `u)
                (Term.hole "_")
                `zero_le_two
                («term_+_» `n "+" (num "1"))
                (Term.fun "fun" (Term.basicFun [`m `hm] [] "=>" (Term.hole "_")))]))
             []
             (Tactic.exact
              "exact"
              (Term.proj
               (Term.proj
                («term_<|_»
                 (Term.app `IH [(Term.hole "_")])
                 "<|"
                 (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm]))
                "."
                (fieldIdx "2"))
               "."
               `le))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app
            (Term.explicit "@" `geom_le)
            [(«term_∘_» `ϕ "∘" `u)
             (Term.hole "_")
             `zero_le_two
             («term_+_» `n "+" (num "1"))
             (Term.fun "fun" (Term.basicFun [`m `hm] [] "=>" (Term.hole "_")))]))
          []
          (Tactic.exact
           "exact"
           (Term.proj
            (Term.proj
             («term_<|_»
              (Term.app `IH [(Term.hole "_")])
              "<|"
              (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm]))
             "."
             (fieldIdx "2"))
            "."
            `le))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.proj
         («term_<|_»
          (Term.app `IH [(Term.hole "_")])
          "<|"
          (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm]))
         "."
         (fieldIdx "2"))
        "."
        `le))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        («term_<|_»
         (Term.app `IH [(Term.hole "_")])
         "<|"
         (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm]))
        "."
        (fieldIdx "2"))
       "."
       `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       («term_<|_»
        (Term.app `IH [(Term.hole "_")])
        "<|"
        (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm]))
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.app `IH [(Term.hole "_")])
       "<|"
       (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Nat.lt_add_one_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `IH [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `IH [(Term.hole "_")])
      "<|"
      (Term.app (Term.proj `Nat.lt_add_one_iff "." (fieldIdx "1")) [`hm]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.explicit "@" `geom_le)
        [(«term_∘_» `ϕ "∘" `u)
         (Term.hole "_")
         `zero_le_two
         («term_+_» `n "+" (num "1"))
         (Term.fun "fun" (Term.basicFun [`m `hm] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `geom_le)
       [(«term_∘_» `ϕ "∘" `u)
        (Term.hole "_")
        `zero_le_two
        («term_+_» `n "+" (num "1"))
        (Term.fun "fun" (Term.basicFun [`m `hm] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`m `hm] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `zero_le_two
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term_∘_» `ϕ "∘" `u)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `ϕ
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_∘_» `ϕ "∘" `u) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `geom_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `geom_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term_*_» («term_^_» (num "2") "^" («term_+_» `n "+" (num "1"))) "*" (Term.app `ϕ [`x]))
       "≤"
       (Term.app `ϕ [(Term.app `u [(«term_+_» `n "+" (num "1"))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ϕ [(Term.app `u [(«term_+_» `n "+" (num "1"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `u [(«term_+_» `n "+" (num "1"))])
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
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `u [(Term.paren "(" («term_+_» `n "+" (num "1")) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» («term_^_» (num "2") "^" («term_+_» `n "+" (num "1"))) "*" (Term.app `ϕ [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ϕ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» (num "2") "^" («term_+_» `n "+" (num "1")))
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
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`A []]
         [(Term.typeSpec
           ":"
           («term_≤_»
            (Term.app (Analysis.Hofer.termd "d") [(Term.app `u [(«term_+_» `n "+" (num "1"))]) `x])
            "≤"
            («term_*_» (num "2") "*" `ε)))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_comm)] "]") [])
             []
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl `r [] [] ":=" (Term.app `range [(«term_+_» `n "+" (num "1"))]))))
             []
             (calcTactic
              "calc"
              (calcStep
               («term_≤_»
                (Term.app
                 (Analysis.Hofer.termd "d")
                 [(Term.app `u [(num "0")]) (Term.app `u [(«term_+_» `n "+" (num "1"))])])
                "≤"
                (BigOperators.Algebra.BigOperators.Basic.finset.sum
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                 " in "
                 `r
                 ", "
                 (Term.app
                  (Analysis.Hofer.termd "d")
                  [(Term.app `u [`i]) («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))])))
               ":="
               (Term.app `dist_le_range_sum_dist [`u («term_+_» `n "+" (num "1"))]))
              [(calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  " in "
                  `r
                  ", "
                  («term_/_» `ε "/" («term_^_» (num "2") "^" `i))))
                ":="
                (Term.app
                 `sum_le_sum
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`i `i_in]
                    []
                    "=>"
                    (Term.proj
                     («term_<|_»
                      (Term.app `IH [`i])
                      "<|"
                      («term_<|_» `nat.lt_succ_iff.mp "<|" (Term.app `finset.mem_range.mp [`i_in])))
                     "."
                     (fieldIdx "1"))))]))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  " in "
                  `r
                  ", "
                  («term_*_» («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i) "*" `ε)))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.congrWith
                     "congr"
                     []
                     "with"
                     [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
                     [])
                    []
                    (Tactic.fieldSimp "field_simp" [] [] [] [] [])]))))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 («term_*_»
                  (BigOperators.Algebra.BigOperators.Basic.finset.sum
                   "∑"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                   " in "
                   `r
                   ", "
                   («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i))
                  "*"
                  `ε))
                ":="
                `finset.sum_mul.symm)
               (calcStep
                («term_≤_» (Term.hole "_") "≤" («term_*_» (num "2") "*" `ε))
                ":="
                (Term.app
                 `mul_le_mul_of_nonneg_right
                 [(Term.app `sum_geometric_two_le [(Term.hole "_")])
                  (Term.app `le_of_lt [`ε_pos])]))])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_comm)] "]") [])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl `r [] [] ":=" (Term.app `range [(«term_+_» `n "+" (num "1"))]))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             (Term.app
              (Analysis.Hofer.termd "d")
              [(Term.app `u [(num "0")]) (Term.app `u [(«term_+_» `n "+" (num "1"))])])
             "≤"
             (BigOperators.Algebra.BigOperators.Basic.finset.sum
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              " in "
              `r
              ", "
              (Term.app
               (Analysis.Hofer.termd "d")
               [(Term.app `u [`i]) («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))])))
            ":="
            (Term.app `dist_le_range_sum_dist [`u («term_+_» `n "+" (num "1"))]))
           [(calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              (BigOperators.Algebra.BigOperators.Basic.finset.sum
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               " in "
               `r
               ", "
               («term_/_» `ε "/" («term_^_» (num "2") "^" `i))))
             ":="
             (Term.app
              `sum_le_sum
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`i `i_in]
                 []
                 "=>"
                 (Term.proj
                  («term_<|_»
                   (Term.app `IH [`i])
                   "<|"
                   («term_<|_» `nat.lt_succ_iff.mp "<|" (Term.app `finset.mem_range.mp [`i_in])))
                  "."
                  (fieldIdx "1"))))]))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (BigOperators.Algebra.BigOperators.Basic.finset.sum
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               " in "
               `r
               ", "
               («term_*_» («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i) "*" `ε)))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.congrWith
                  "congr"
                  []
                  "with"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
                  [])
                 []
                 (Tactic.fieldSimp "field_simp" [] [] [] [] [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                " in "
                `r
                ", "
                («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i))
               "*"
               `ε))
             ":="
             `finset.sum_mul.symm)
            (calcStep
             («term_≤_» (Term.hole "_") "≤" («term_*_» (num "2") "*" `ε))
             ":="
             (Term.app
              `mul_le_mul_of_nonneg_right
              [(Term.app `sum_geometric_two_le [(Term.hole "_")])
               (Term.app `le_of_lt [`ε_pos])]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (Term.app
          (Analysis.Hofer.termd "d")
          [(Term.app `u [(num "0")]) (Term.app `u [(«term_+_» `n "+" (num "1"))])])
         "≤"
         (BigOperators.Algebra.BigOperators.Basic.finset.sum
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          " in "
          `r
          ", "
          (Term.app
           (Analysis.Hofer.termd "d")
           [(Term.app `u [`i]) («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))])))
        ":="
        (Term.app `dist_le_range_sum_dist [`u («term_+_» `n "+" (num "1"))]))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          (BigOperators.Algebra.BigOperators.Basic.finset.sum
           "∑"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           " in "
           `r
           ", "
           («term_/_» `ε "/" («term_^_» (num "2") "^" `i))))
         ":="
         (Term.app
          `sum_le_sum
          [(Term.fun
            "fun"
            (Term.basicFun
             [`i `i_in]
             []
             "=>"
             (Term.proj
              («term_<|_»
               (Term.app `IH [`i])
               "<|"
               («term_<|_» `nat.lt_succ_iff.mp "<|" (Term.app `finset.mem_range.mp [`i_in])))
              "."
              (fieldIdx "1"))))]))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (BigOperators.Algebra.BigOperators.Basic.finset.sum
           "∑"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           " in "
           `r
           ", "
           («term_*_» («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i) "*" `ε)))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.congrWith
              "congr"
              []
              "with"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
              [])
             []
             (Tactic.fieldSimp "field_simp" [] [] [] [] [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (BigOperators.Algebra.BigOperators.Basic.finset.sum
            "∑"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
            " in "
            `r
            ", "
            («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i))
           "*"
           `ε))
         ":="
         `finset.sum_mul.symm)
        (calcStep
         («term_≤_» (Term.hole "_") "≤" («term_*_» (num "2") "*" `ε))
         ":="
         (Term.app
          `mul_le_mul_of_nonneg_right
          [(Term.app `sum_geometric_two_le [(Term.hole "_")]) (Term.app `le_of_lt [`ε_pos])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_le_mul_of_nonneg_right
       [(Term.app `sum_geometric_two_le [(Term.hole "_")]) (Term.app `le_of_lt [`ε_pos])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_lt [`ε_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_of_lt [`ε_pos]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `sum_geometric_two_le [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sum_geometric_two_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `sum_geometric_two_le [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_of_nonneg_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.hole "_") "≤" («term_*_» (num "2") "*" `ε))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (num "2") "*" `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      `finset.sum_mul.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        (BigOperators.Algebra.BigOperators.Basic.finset.sum
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         " in "
         `r
         ", "
         («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i))
        "*"
        `ε))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        `r
        ", "
        («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i))
       "*"
       `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       `r
       ", "
       («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_/_» (num "1") "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_/_» (num "1") "/" (num "2")) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.sum
      "∑"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
      " in "
      `r
      ", "
      («term_^_» (Term.paren "(" («term_/_» (num "1") "/" (num "2")) ")") "^" `i))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.congrWith
           "congr"
           []
           "with"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
           [])
          []
          (Tactic.fieldSimp "field_simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp "field_simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.congrWith
       "congr"
       []
       "with"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        `r
        ", "
        («term_*_» («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i) "*" `ε)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       `r
       ", "
       («term_*_» («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i) "*" `ε))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i) "*" `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» («term_/_» (num "1") "/" (num "2")) "^" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_/_» (num "1") "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_/_» (num "1") "/" (num "2")) ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app
       `sum_le_sum
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i `i_in]
          []
          "=>"
          (Term.proj
           («term_<|_»
            (Term.app `IH [`i])
            "<|"
            («term_<|_» `nat.lt_succ_iff.mp "<|" (Term.app `finset.mem_range.mp [`i_in])))
           "."
           (fieldIdx "1"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i `i_in]
        []
        "=>"
        (Term.proj
         («term_<|_»
          (Term.app `IH [`i])
          "<|"
          («term_<|_» `nat.lt_succ_iff.mp "<|" (Term.app `finset.mem_range.mp [`i_in])))
         "."
         (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       («term_<|_»
        (Term.app `IH [`i])
        "<|"
        («term_<|_» `nat.lt_succ_iff.mp "<|" (Term.app `finset.mem_range.mp [`i_in])))
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.app `IH [`i])
       "<|"
       («term_<|_» `nat.lt_succ_iff.mp "<|" (Term.app `finset.mem_range.mp [`i_in])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `nat.lt_succ_iff.mp "<|" (Term.app `finset.mem_range.mp [`i_in]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `finset.mem_range.mp [`i_in])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i_in
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `finset.mem_range.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `nat.lt_succ_iff.mp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `IH [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `IH [`i])
      "<|"
      («term_<|_» `nat.lt_succ_iff.mp "<|" (Term.app `finset.mem_range.mp [`i_in])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i_in
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sum_le_sum
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        `r
        ", "
        («term_/_» `ε "/" («term_^_» (num "2") "^" `i))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       `r
       ", "
       («term_/_» `ε "/" («term_^_» (num "2") "^" `i)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" («term_^_» (num "2") "^" `i))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "2") "^" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `dist_le_range_sum_dist [`u («term_+_» `n "+" (num "1"))])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist_le_range_sum_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.app
        (Analysis.Hofer.termd "d")
        [(Term.app `u [(num "0")]) (Term.app `u [(«term_+_» `n "+" (num "1"))])])
       "≤"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        `r
        ", "
        (Term.app
         (Analysis.Hofer.termd "d")
         [(Term.app `u [`i]) («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       `r
       ", "
       (Term.app
        (Analysis.Hofer.termd "d")
        [(Term.app `u [`i]) («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Analysis.Hofer.termd "d")
       [(Term.app `u [`i]) («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `i "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `u "<|" («term_+_» `i "+" (num "1")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `u [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `u [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Analysis.Hofer.termd "d")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Hofer.termd', expected 'Analysis.Hofer.termd._@.Analysis.Hofer._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
  hofer
  { X : Type _ }
      [ MetricSpace X ]
      [ CompleteSpace X ]
      ( x : X )
      ( ε : ℝ )
      ( ε_pos : 0 < ε )
      { ϕ : X → ℝ }
      ( cont : Continuous ϕ )
      ( nonneg : ∀ y , 0 ≤ ϕ y )
    :
      ∃
        ε'
        > 0
        ,
        ∃
          x' : X
          ,
          ε' ≤ ε ∧ d x' x ≤ 2 * ε ∧ ε * ϕ x ≤ ε' * ϕ x' ∧ ∀ y , d x' y ≤ ε' → ϕ y ≤ 2 * ϕ x'
  :=
    by
      by_contra H
        have
          reformulation
            : ∀ ( x' ) ( k : ℕ ) , ε * ϕ x ≤ ε / 2 ^ k * ϕ x' ↔ 2 ^ k * ϕ x ≤ ϕ x'
            :=
            by
              intro x' k
                rw
                  [ div_mul_eq_mul_div , le_div_iff , mul_assoc , mul_le_mul_left ε_pos , mul_comm ]
                positivity
        replace
          H
          :
            ∀
              k
              : ℕ
              ,
              ∀ x' , d x' x ≤ 2 * ε ∧ 2 ^ k * ϕ x ≤ ϕ x' → ∃ y , d x' y ≤ ε / 2 ^ k ∧ 2 * ϕ x' < ϕ y
        ·
          intro k x'
            push_neg at H
            simpa
              [ reformulation ]
                using H ε / 2 ^ k by simp [ ε_pos ] x' by simp [ ε_pos.le , one_le_two ]
        clear reformulation
        haveI : Nonempty X := ⟨ x ⟩
        choose! F hF using H
        let u : ℕ → X := fun n => Nat.recOn n x F
        have hu0 : u 0 = x := rfl
        have
          hu
            :
              ∀
                n
                ,
                d u n x ≤ 2 * ε ∧ 2 ^ n * ϕ x ≤ ϕ u n
                  →
                  d u n u <| n + 1 ≤ ε / 2 ^ n ∧ 2 * ϕ u n < ϕ u <| n + 1
            :=
            by intro n exact hF n u n
        clear hF
        have
          key
            : ∀ n , d u n u n + 1 ≤ ε / 2 ^ n ∧ 2 * ϕ u n < ϕ u n + 1
            :=
            by
              intro n
                induction' n using Nat.case_strong_induction_on with n IH
                ·
                  specialize hu 0
                    simpa [ hu0 , mul_nonneg_iff , zero_le_one , ε_pos.le , le_refl ] using hu
                have
                  A
                    : d u n + 1 x ≤ 2 * ε
                    :=
                    by
                      rw [ dist_comm ]
                        let r := range n + 1
                        calc
                          d u 0 u n + 1 ≤ ∑ i in r , d u i u <| i + 1
                            :=
                            dist_le_range_sum_dist u n + 1
                          _ ≤ ∑ i in r , ε / 2 ^ i
                              :=
                              sum_le_sum
                                fun
                                  i i_in
                                    =>
                                    IH i <| nat.lt_succ_iff.mp <| finset.mem_range.mp i_in . 1
                            _ = ∑ i in r , 1 / 2 ^ i * ε := by congr with i field_simp
                            _ = ∑ i in r , 1 / 2 ^ i * ε := finset.sum_mul.symm
                            _ ≤ 2 * ε
                              :=
                              mul_le_mul_of_nonneg_right sum_geometric_two_le _ le_of_lt ε_pos
                have
                  B
                    : 2 ^ n + 1 * ϕ x ≤ ϕ u n + 1
                    :=
                    by
                      refine' @ geom_le ϕ ∘ u _ zero_le_two n + 1 fun m hm => _
                        exact IH _ <| Nat.lt_add_one_iff . 1 hm . 2 . le
                exact hu n + 1 ⟨ A , B ⟩
        cases' forall_and_distrib.mp key with key₁ key₂
        clear hu key
        have
          cauchy_u
            : CauchySeq u
            :=
            by
              refine' cauchy_seq_of_le_geometric _ ε one_half_lt_one fun n => _
                simpa only [ one_div , inv_pow ] using key₁ n
        obtain ⟨ y , limy ⟩ : ∃ y , tendsto u at_top 𝓝 y
        exact CompleteSpace.complete cauchy_u
        have
          lim_top
            : tendsto ϕ ∘ u at_top at_top
            :=
            by
              let v n := ϕ ∘ u n + 1
                suffices tendsto v at_top at_top by rwa [ tendsto_add_at_top_iff_nat ] at this
                have
                  hv₀
                    : 0 < v 0
                    :=
                    by
                      have : 0 ≤ ϕ u 0 := nonneg x
                        calc 0 ≤ 2 * ϕ u 0 := by linarith _ < ϕ u 0 + 1 := key₂ 0
                apply tendsto_at_top_of_geom_le hv₀ one_lt_two
                exact fun n => key₂ n + 1 . le
        have lim : tendsto ϕ ∘ u at_top 𝓝 ϕ y := tendsto.comp cont.continuous_at limy
        exact not_tendsto_at_top_of_tendsto_nhds lim lim_top
#align hofer hofer

