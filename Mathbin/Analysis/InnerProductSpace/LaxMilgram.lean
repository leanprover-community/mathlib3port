/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González

! This file was ported from Lean 3 source module analysis.inner_product_space.lax_milgram
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Analysis.InnerProductSpace.Dual
import Mathbin.Analysis.NormedSpace.Banach
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Topology.MetricSpace.Antilipschitz

/-!
# The Lax-Milgram Theorem

We consider an Hilbert space `V` over `ℝ`
equipped with a bounded bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`.

Recall that a bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ` is *coercive*
iff `∃ C, (0 < C) ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u`.
Under the hypothesis that `B` is coercive
we prove the Lax-Milgram theorem:
that is, the map `inner_product_space.continuous_linear_map_of_bilin` from
`analysis.inner_product_space.dual` can be upgraded to a continuous equivalence
`is_coercive.continuous_linear_equiv_of_bilin : V ≃L[ℝ] V`.

## References

* We follow the notes of Peter Howard's Spring 2020 *M612: Partial Differential Equations* lecture,
  see[howard]

## Tags

dual, Lax-Milgram
-/


noncomputable section

open IsROrC LinearMap ContinuousLinearMap InnerProductSpace

open LinearMap (ker range)

open RealInnerProductSpace Nnreal

universe u

namespace IsCoercive

variable {V : Type u} [InnerProductSpace ℝ V] [CompleteSpace V]

variable {B : V →L[ℝ] V →L[ℝ] ℝ}

-- mathport name: «expr ♯»
local postfix:1024 "♯" => @continuousLinearMapOfBilin ℝ V _ _ _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `bounded_below [])
      (Command.declSig
       [(Term.explicitBinder "(" [`coercive] [":" (Term.app `IsCoercive [`B])] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `C)] []))
         ","
         («term_∧_»
          («term_<_» (num "0") "<" `C)
          "∧"
          (Term.forall
           "∀"
           [`v]
           []
           ","
           («term_≤_»
            («term_*_» `C "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖"))
            "≤"
            (Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
             "‖")))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `coercive)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C_ge_0)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `coercivity)])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor "⟨" [`C "," `C_ge_0 "," (Term.hole "_")] "⟩"))
           []
           (Tactic.intro "intro" [`v])
           []
           (Classical.«tacticBy_cases_:_»
            "by_cases"
            [`h ":"]
            («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖")))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine'
              "refine'"
              (Term.app (Term.proj (Term.app `mul_le_mul_right [`h]) "." `mp) [(Term.hole "_")]))
             []
             (calcTactic
              "calc"
              (calcStep
               («term_≤_»
                («term_*_»
                 («term_*_» `C "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖"))
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖"))
                "≤"
                (Term.app `B [`v `v]))
               ":="
               (Term.app `coercivity [`v]))
              [(calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
                  "⟪"
                  (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
                  ", "
                  `v
                  "⟫_ℝ"))
                ":="
                (Term.proj
                 (Term.app
                  `continuous_linear_map_of_bilin_apply
                  [(Data.Real.Basic.termℝ "ℝ") `B `v `v])
                 "."
                 `symm))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 («term_*_»
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   (Term.app
                    (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
                    [`v])
                   "‖")
                  "*"
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖")))
                ":="
                (Term.app
                 `real_inner_le_norm
                 [(Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
                  `v]))])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" («term_=_» `v "=" (num "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.Simpa.simpa
                     "simpa"
                     []
                     []
                     (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h]))]))))))
             []
             (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] [])])])))
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
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `coercive)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C_ge_0)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `coercivity)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor "⟨" [`C "," `C_ge_0 "," (Term.hole "_")] "⟩"))
          []
          (Tactic.intro "intro" [`v])
          []
          (Classical.«tacticBy_cases_:_»
           "by_cases"
           [`h ":"]
           («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.app (Term.proj (Term.app `mul_le_mul_right [`h]) "." `mp) [(Term.hole "_")]))
            []
            (calcTactic
             "calc"
             (calcStep
              («term_≤_»
               («term_*_»
                («term_*_» `C "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖"))
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖"))
               "≤"
               (Term.app `B [`v `v]))
              ":="
              (Term.app `coercivity [`v]))
             [(calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
                 "⟪"
                 (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
                 ", "
                 `v
                 "⟫_ℝ"))
               ":="
               (Term.proj
                (Term.app
                 `continuous_linear_map_of_bilin_apply
                 [(Data.Real.Basic.termℝ "ℝ") `B `v `v])
                "."
                `symm))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_*_»
                 (Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
                  "‖")
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖")))
               ":="
               (Term.app
                `real_inner_le_norm
                [(Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
                 `v]))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" («term_=_» `v "=" (num "0")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.Simpa.simpa
                    "simpa"
                    []
                    []
                    (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h]))]))))))
            []
            (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" («term_=_» `v "=" (num "0")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h]))]))))))
        []
        (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_=_» `v "=" (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `v "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.app (Term.proj (Term.app `mul_le_mul_right [`h]) "." `mp) [(Term.hole "_")]))
        []
        (calcTactic
         "calc"
         (calcStep
          («term_≤_»
           («term_*_»
            («term_*_» `C "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖"))
            "*"
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖"))
           "≤"
           (Term.app `B [`v `v]))
          ":="
          (Term.app `coercivity [`v]))
         [(calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
             "⟪"
             (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
             ", "
             `v
             "⟫_ℝ"))
           ":="
           (Term.proj
            (Term.app `continuous_linear_map_of_bilin_apply [(Data.Real.Basic.termℝ "ℝ") `B `v `v])
            "."
            `symm))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            («term_*_»
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
              "‖")
             "*"
             (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖")))
           ":="
           (Term.app
            `real_inner_le_norm
            [(Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
             `v]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         («term_*_»
          («term_*_» `C "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖"))
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖"))
         "≤"
         (Term.app `B [`v `v]))
        ":="
        (Term.app `coercivity [`v]))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
           "⟪"
           (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
           ", "
           `v
           "⟫_ℝ"))
         ":="
         (Term.proj
          (Term.app `continuous_linear_map_of_bilin_apply [(Data.Real.Basic.termℝ "ℝ") `B `v `v])
          "."
          `symm))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
            "‖")
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖")))
         ":="
         (Term.app
          `real_inner_le_norm
          [(Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
           `v]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `real_inner_le_norm
       [(Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v]) `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.term_♯._@.Analysis.InnerProductSpace.LaxMilgram._hyg.10'
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
  bounded_below
  ( coercive : IsCoercive B ) : ∃ C , 0 < C ∧ ∀ v , C * ‖ v ‖ ≤ ‖ B ♯ v ‖
  :=
    by
      rcases coercive with ⟨ C , C_ge_0 , coercivity ⟩
        refine' ⟨ C , C_ge_0 , _ ⟩
        intro v
        by_cases h : 0 < ‖ v ‖
        ·
          refine' mul_le_mul_right h . mp _
            calc
              C * ‖ v ‖ * ‖ v ‖ ≤ B v v := coercivity v
              _ = ⟪ B ♯ v , v ⟫_ℝ := continuous_linear_map_of_bilin_apply ℝ B v v . symm
                _ ≤ ‖ B ♯ v ‖ * ‖ v ‖ := real_inner_le_norm B ♯ v v
        · have : v = 0 := by simpa using h simp [ this ]
#align is_coercive.bounded_below IsCoercive.bounded_below

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `antilipschitz [])
      (Command.declSig
       [(Term.explicitBinder "(" [`coercive] [":" (Term.app `IsCoercive [`B])] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `C)]
           [":" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")]))
         ","
         («term_∧_»
          («term_<_» (num "0") "<" `C)
          "∧"
          (Term.app
           `AntilipschitzWith
           [`C (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `coercive.bounded_below)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C_pos)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `below_bound)])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.proj («term_⁻¹» `C "⁻¹") "." `toNnreal)
              ","
              (Term.app `real.to_nnreal_pos.mpr [(Term.app `inv_pos.mpr [`C_pos])])
              ","
              (Term.hole "_")]
             "⟩"))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `ContinuousLinearMap.antilipschitz_of_bound
             [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") (Term.hole "_")]))
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Real.coe_to_nnreal')
              ","
              (Tactic.rwRule [] (Term.app `max_eq_left_of_lt [(Term.app `inv_pos.mpr [`C_pos])]))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `inv_mul_le_iff [(Term.app `inv_pos.mpr [`C_pos])]))]
             "]")
            [])
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `below_bound]))])))
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
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `coercive.bounded_below)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C_pos)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `below_bound)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.proj («term_⁻¹» `C "⁻¹") "." `toNnreal)
             ","
             (Term.app `real.to_nnreal_pos.mpr [(Term.app `inv_pos.mpr [`C_pos])])
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `ContinuousLinearMap.antilipschitz_of_bound
            [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") (Term.hole "_")]))
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Real.coe_to_nnreal')
             ","
             (Tactic.rwRule [] (Term.app `max_eq_left_of_lt [(Term.app `inv_pos.mpr [`C_pos])]))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `inv_mul_le_iff [(Term.app `inv_pos.mpr [`C_pos])]))]
            "]")
           [])
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `below_bound]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `below_bound]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `below_bound
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Real.coe_to_nnreal')
         ","
         (Tactic.rwRule [] (Term.app `max_eq_left_of_lt [(Term.app `inv_pos.mpr [`C_pos])]))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `inv_mul_le_iff [(Term.app `inv_pos.mpr [`C_pos])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inv_mul_le_iff [(Term.app `inv_pos.mpr [`C_pos])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inv_pos.mpr [`C_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv_pos.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `inv_pos.mpr [`C_pos]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv_mul_le_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `max_eq_left_of_lt [(Term.app `inv_pos.mpr [`C_pos])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inv_pos.mpr [`C_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv_pos.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `inv_pos.mpr [`C_pos]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `max_eq_left_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.coe_to_nnreal'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `ContinuousLinearMap.antilipschitz_of_bound
        [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ContinuousLinearMap.antilipschitz_of_bound
       [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.term_♯._@.Analysis.InnerProductSpace.LaxMilgram._hyg.10'
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
  antilipschitz
  ( coercive : IsCoercive B ) : ∃ C : ℝ≥0 , 0 < C ∧ AntilipschitzWith C B ♯
  :=
    by
      rcases coercive.bounded_below with ⟨ C , C_pos , below_bound ⟩
        refine' ⟨ C ⁻¹ . toNnreal , real.to_nnreal_pos.mpr inv_pos.mpr C_pos , _ ⟩
        refine' ContinuousLinearMap.antilipschitz_of_bound B ♯ _
        simp_rw
          [
            Real.coe_to_nnreal'
              ,
              max_eq_left_of_lt inv_pos.mpr C_pos
              ,
              ← inv_mul_le_iff inv_pos.mpr C_pos
            ]
        simpa using below_bound
#align is_coercive.antilipschitz IsCoercive.antilipschitz

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ker_eq_bot [])
      (Command.declSig
       [(Term.explicitBinder "(" [`coercive] [":" (Term.app `IsCoercive [`B])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `ker [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")])
         "="
         (Order.BoundedOrder.«term⊥» "⊥"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearMapClass.ker_eq_bot)] "]")
            [])
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `coercive.antilipschitz)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.one `antilipschitz)])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.exact "exact" `antilipschitz.injective)])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearMapClass.ker_eq_bot)] "]")
           [])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `coercive.antilipschitz)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.one `antilipschitz)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.exact "exact" `antilipschitz.injective)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `antilipschitz.injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `antilipschitz.injective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `coercive.antilipschitz)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `antilipschitz)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coercive.antilipschitz
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearMapClass.ker_eq_bot)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMapClass.ker_eq_bot
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `ker [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")])
       "="
       (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `ker [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.term_♯._@.Analysis.InnerProductSpace.LaxMilgram._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  ker_eq_bot
  ( coercive : IsCoercive B ) : ker B ♯ = ⊥
  :=
    by
      rw [ LinearMapClass.ker_eq_bot ]
        rcases coercive.antilipschitz with ⟨ _ , _ , antilipschitz ⟩
        exact antilipschitz.injective
#align is_coercive.ker_eq_bot IsCoercive.ker_eq_bot

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `closed_range [])
      (Command.declSig
       [(Term.explicitBinder "(" [`coercive] [":" (Term.app `IsCoercive [`B])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `IsClosed
         [(Term.typeAscription
           "("
           (Term.app `range [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")])
           ":"
           [(Term.app `Set [`V])]
           ")")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `coercive.antilipschitz)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.one `antilipschitz)])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `antilipschitz.is_closed_range
             [(Term.proj
               (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
               "."
               `UniformContinuous)]))])))
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
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `coercive.antilipschitz)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.one `antilipschitz)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `antilipschitz.is_closed_range
            [(Term.proj
              (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
              "."
              `UniformContinuous)]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `antilipschitz.is_closed_range
        [(Term.proj
          (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
          "."
          `UniformContinuous)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `antilipschitz.is_closed_range
       [(Term.proj
         (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
         "."
         `UniformContinuous)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
       "."
       `UniformContinuous)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.term_♯._@.Analysis.InnerProductSpace.LaxMilgram._hyg.10'
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
  closed_range
  ( coercive : IsCoercive B ) : IsClosed ( range B ♯ : Set V )
  :=
    by
      rcases coercive.antilipschitz with ⟨ _ , _ , antilipschitz ⟩
        exact antilipschitz.is_closed_range B ♯ . UniformContinuous
#align is_coercive.closed_range IsCoercive.closed_range

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `range_eq_top [])
      (Command.declSig
       [(Term.explicitBinder "(" [`coercive] [":" (Term.app `IsCoercive [`B])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `range [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")])
         "="
         (Order.BoundedOrder.«term⊤» "⊤"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl (Term.haveIdDecl [] [] ":=" `coercive.closed_range.complete_space_coe)))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.proj
                (Term.app
                 `range
                 [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")])
                "."
                `orthogonal_orthogonal))]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.eq_top_iff')] "]")
            [])
           []
           (Tactic.intro "intro" [`v `w `mem_w_orthogonal])
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `coercive)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C_pos)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `coercivity)])
                   [])]
                 "⟩")])
              [])])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])]
            [":" («term_=_» `w "=" (num "0"))]
            [":="
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_self_eq_zero)
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `mul_right_inj' [`C_pos.ne']))
                     ","
                     (Tactic.rwRule [] `mul_zero)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)]
                    "]")
                   [])
                  []
                  (Tactic.apply "apply" `le_antisymm)
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(calcTactic
                     "calc"
                     (calcStep
                      («term_≤_»
                       («term_*_»
                        («term_*_» `C "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
                        "*"
                        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
                       "≤"
                       (Term.app `B [`w `w]))
                      ":="
                      (Term.app `coercivity [`w]))
                     [(calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
                         "⟪"
                         (Term.app
                          (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
                          [`w])
                         ", "
                         `w
                         "⟫_ℝ"))
                       ":="
                       (Term.proj
                        (Term.app
                         `continuous_linear_map_of_bilin_apply
                         [(Data.Real.Basic.termℝ "ℝ") `B `w `w])
                        "."
                        `symm))
                      (calcStep
                       («term_=_» (Term.hole "_") "=" (num "0"))
                       ":="
                       (Term.app
                        `mem_w_orthogonal
                        [(Term.hole "_") (Term.anonymousCtor "⟨" [`w "," `rfl] "⟩")]))])])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.exact
                     "exact"
                     (Term.app
                      `mul_nonneg
                      [(Term.app `mul_nonneg [`C_pos.le (Term.app `norm_nonneg [`w])])
                       (Term.app `norm_nonneg [`w])]))])])))]])
           []
           (Tactic.exact "exact" `inner_zero_left)])))
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
           (Term.haveDecl (Term.haveIdDecl [] [] ":=" `coercive.closed_range.complete_space_coe)))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.proj
               (Term.app
                `range
                [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")])
               "."
               `orthogonal_orthogonal))]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.eq_top_iff')] "]")
           [])
          []
          (Tactic.intro "intro" [`v `w `mem_w_orthogonal])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `coercive)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C_pos)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `coercivity)])
                  [])]
                "⟩")])
             [])])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])]
           [":" («term_=_» `w "=" (num "0"))]
           [":="
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_self_eq_zero)
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `mul_right_inj' [`C_pos.ne']))
                    ","
                    (Tactic.rwRule [] `mul_zero)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)]
                   "]")
                  [])
                 []
                 (Tactic.apply "apply" `le_antisymm)
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(calcTactic
                    "calc"
                    (calcStep
                     («term_≤_»
                      («term_*_»
                       («term_*_» `C "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
                       "*"
                       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
                      "≤"
                      (Term.app `B [`w `w]))
                     ":="
                     (Term.app `coercivity [`w]))
                    [(calcStep
                      («term_=_»
                       (Term.hole "_")
                       "="
                       (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
                        "⟪"
                        (Term.app
                         (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
                         [`w])
                        ", "
                        `w
                        "⟫_ℝ"))
                      ":="
                      (Term.proj
                       (Term.app
                        `continuous_linear_map_of_bilin_apply
                        [(Data.Real.Basic.termℝ "ℝ") `B `w `w])
                       "."
                       `symm))
                     (calcStep
                      («term_=_» (Term.hole "_") "=" (num "0"))
                      ":="
                      (Term.app
                       `mem_w_orthogonal
                       [(Term.hole "_") (Term.anonymousCtor "⟨" [`w "," `rfl] "⟩")]))])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app
                     `mul_nonneg
                     [(Term.app `mul_nonneg [`C_pos.le (Term.app `norm_nonneg [`w])])
                      (Term.app `norm_nonneg [`w])]))])])))]])
          []
          (Tactic.exact "exact" `inner_zero_left)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `inner_zero_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_zero_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])]
       [":" («term_=_» `w "=" (num "0"))]
       [":="
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_self_eq_zero)
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `mul_right_inj' [`C_pos.ne']))
                ","
                (Tactic.rwRule [] `mul_zero)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)]
               "]")
              [])
             []
             (Tactic.apply "apply" `le_antisymm)
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(calcTactic
                "calc"
                (calcStep
                 («term_≤_»
                  («term_*_»
                   («term_*_» `C "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
                  "≤"
                  (Term.app `B [`w `w]))
                 ":="
                 (Term.app `coercivity [`w]))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
                    "⟪"
                    (Term.app
                     (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
                     [`w])
                    ", "
                    `w
                    "⟫_ℝ"))
                  ":="
                  (Term.proj
                   (Term.app
                    `continuous_linear_map_of_bilin_apply
                    [(Data.Real.Basic.termℝ "ℝ") `B `w `w])
                   "."
                   `symm))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" (num "0"))
                  ":="
                  (Term.app
                   `mem_w_orthogonal
                   [(Term.hole "_") (Term.anonymousCtor "⟨" [`w "," `rfl] "⟩")]))])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.app
                 `mul_nonneg
                 [(Term.app `mul_nonneg [`C_pos.le (Term.app `norm_nonneg [`w])])
                  (Term.app `norm_nonneg [`w])]))])])))]])
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_self_eq_zero)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `mul_right_inj' [`C_pos.ne']))
             ","
             (Tactic.rwRule [] `mul_zero)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)]
            "]")
           [])
          []
          (Tactic.apply "apply" `le_antisymm)
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(calcTactic
             "calc"
             (calcStep
              («term_≤_»
               («term_*_»
                («term_*_» `C "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
               "≤"
               (Term.app `B [`w `w]))
              ":="
              (Term.app `coercivity [`w]))
             [(calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
                 "⟪"
                 (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`w])
                 ", "
                 `w
                 "⟫_ℝ"))
               ":="
               (Term.proj
                (Term.app
                 `continuous_linear_map_of_bilin_apply
                 [(Data.Real.Basic.termℝ "ℝ") `B `w `w])
                "."
                `symm))
              (calcStep
               («term_=_» (Term.hole "_") "=" (num "0"))
               ":="
               (Term.app
                `mem_w_orthogonal
                [(Term.hole "_") (Term.anonymousCtor "⟨" [`w "," `rfl] "⟩")]))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `mul_nonneg
              [(Term.app `mul_nonneg [`C_pos.le (Term.app `norm_nonneg [`w])])
               (Term.app `norm_nonneg [`w])]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          `mul_nonneg
          [(Term.app `mul_nonneg [`C_pos.le (Term.app `norm_nonneg [`w])])
           (Term.app `norm_nonneg [`w])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `mul_nonneg
        [(Term.app `mul_nonneg [`C_pos.le (Term.app `norm_nonneg [`w])])
         (Term.app `norm_nonneg [`w])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_nonneg
       [(Term.app `mul_nonneg [`C_pos.le (Term.app `norm_nonneg [`w])])
        (Term.app `norm_nonneg [`w])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_nonneg [`w])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `norm_nonneg [`w]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mul_nonneg [`C_pos.le (Term.app `norm_nonneg [`w])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_nonneg [`w])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `norm_nonneg [`w]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `C_pos.le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mul_nonneg [`C_pos.le (Term.paren "(" (Term.app `norm_nonneg [`w]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(calcTactic
         "calc"
         (calcStep
          («term_≤_»
           («term_*_»
            («term_*_» `C "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
            "*"
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
           "≤"
           (Term.app `B [`w `w]))
          ":="
          (Term.app `coercivity [`w]))
         [(calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
             "⟪"
             (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`w])
             ", "
             `w
             "⟫_ℝ"))
           ":="
           (Term.proj
            (Term.app `continuous_linear_map_of_bilin_apply [(Data.Real.Basic.termℝ "ℝ") `B `w `w])
            "."
            `symm))
          (calcStep
           («term_=_» (Term.hole "_") "=" (num "0"))
           ":="
           (Term.app
            `mem_w_orthogonal
            [(Term.hole "_") (Term.anonymousCtor "⟨" [`w "," `rfl] "⟩")]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         («term_*_»
          («term_*_» `C "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `w "‖"))
         "≤"
         (Term.app `B [`w `w]))
        ":="
        (Term.app `coercivity [`w]))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
           "⟪"
           (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`w])
           ", "
           `w
           "⟫_ℝ"))
         ":="
         (Term.proj
          (Term.app `continuous_linear_map_of_bilin_apply [(Data.Real.Basic.termℝ "ℝ") `B `w `w])
          "."
          `symm))
        (calcStep
         («term_=_» (Term.hole "_") "=" (num "0"))
         ":="
         (Term.app
          `mem_w_orthogonal
          [(Term.hole "_") (Term.anonymousCtor "⟨" [`w "," `rfl] "⟩")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_w_orthogonal [(Term.hole "_") (Term.anonymousCtor "⟨" [`w "," `rfl] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`w "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_w_orthogonal
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
      (Term.proj
       (Term.app `continuous_linear_map_of_bilin_apply [(Data.Real.Basic.termℝ "ℝ") `B `w `w])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `continuous_linear_map_of_bilin_apply [(Data.Real.Basic.termℝ "ℝ") `B `w `w])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_linear_map_of_bilin_apply
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `continuous_linear_map_of_bilin_apply [(Data.Real.Basic.termℝ "ℝ") `B `w `w])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
        "⟪"
        (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`w])
        ", "
        `w
        "⟫_ℝ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ»
       "⟪"
       (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`w])
       ", "
       `w
       "⟫_ℝ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯") [`w])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.term_♯._@.Analysis.InnerProductSpace.LaxMilgram._hyg.10'
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
  range_eq_top
  ( coercive : IsCoercive B ) : range B ♯ = ⊤
  :=
    by
      haveI := coercive.closed_range.complete_space_coe
        rw [ ← range B ♯ . orthogonal_orthogonal ]
        rw [ Submodule.eq_top_iff' ]
        intro v w mem_w_orthogonal
        rcases coercive with ⟨ C , C_pos , coercivity ⟩
        obtain
          rfl
          : w = 0
          :=
            by
              rw
                  [
                    ← norm_eq_zero
                      ,
                      ← mul_self_eq_zero
                      ,
                      ← mul_right_inj' C_pos.ne'
                      ,
                      mul_zero
                      ,
                      ← mul_assoc
                    ]
                apply le_antisymm
                ·
                  calc
                    C * ‖ w ‖ * ‖ w ‖ ≤ B w w := coercivity w
                    _ = ⟪ B ♯ w , w ⟫_ℝ := continuous_linear_map_of_bilin_apply ℝ B w w . symm
                      _ = 0 := mem_w_orthogonal _ ⟨ w , rfl ⟩
                · exact mul_nonneg mul_nonneg C_pos.le norm_nonneg w norm_nonneg w
        exact inner_zero_left
#align is_coercive.range_eq_top IsCoercive.range_eq_top

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The Lax-Milgram equivalence of a coercive bounded bilinear operator:\nfor all `v : V`, `continuous_linear_equiv_of_bilin B v` is the unique element `V`\nsuch that `⟪continuous_linear_equiv_of_bilin B v, w⟫ = B v w`.\nThe Lax-Milgram theorem states that this is a continuous equivalence.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `continuousLinearEquivOfBilin [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`coercive] [":" (Term.app `IsCoercive [`B])] [] ")")]
       [(Term.typeSpec
         ":"
         (Topology.Algebra.Module.Basic.«term_≃L[_]_»
          `V
          " ≃L["
          (Data.Real.Basic.termℝ "ℝ")
          "] "
          `V))])
      (Command.declValSimple
       ":="
       (Term.app
        `ContinuousLinearEquiv.ofBijective
        [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
         (Term.proj `coercive "." `ker_eq_bot)
         (Term.proj `coercive "." `range_eq_top)])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ContinuousLinearEquiv.ofBijective
       [(IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
        (Term.proj `coercive "." `ker_eq_bot)
        (Term.proj `coercive "." `range_eq_top)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `coercive "." `range_eq_top)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coercive
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `coercive "." `ker_eq_bot)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coercive
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯» `B "♯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.«term_♯»', expected 'IsCoercive.Analysis.InnerProductSpace.LaxMilgram.term_♯._@.Analysis.InnerProductSpace.LaxMilgram._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The Lax-Milgram equivalence of a coercive bounded bilinear operator:
    for all `v : V`, `continuous_linear_equiv_of_bilin B v` is the unique element `V`
    such that `⟪continuous_linear_equiv_of_bilin B v, w⟫ = B v w`.
    The Lax-Milgram theorem states that this is a continuous equivalence.
    -/
  def
    continuousLinearEquivOfBilin
    ( coercive : IsCoercive B ) : V ≃L[ ℝ ] V
    := ContinuousLinearEquiv.ofBijective B ♯ coercive . ker_eq_bot coercive . range_eq_top
#align is_coercive.continuous_linear_equiv_of_bilin IsCoercive.continuousLinearEquivOfBilin

@[simp]
theorem continuous_linear_equiv_of_bilin_apply (coercive : IsCoercive B) (v w : V) :
    ⟪coercive.continuousLinearEquivOfBilin v, w⟫_ℝ = B v w :=
  continuous_linear_map_of_bilin_apply ℝ B v w
#align
  is_coercive.continuous_linear_equiv_of_bilin_apply IsCoercive.continuous_linear_equiv_of_bilin_apply

theorem unique_continuous_linear_equiv_of_bilin (coercive : IsCoercive B) {v f : V}
    (is_lax_milgram : ∀ w, ⟪f, w⟫_ℝ = B v w) : f = coercive.continuousLinearEquivOfBilin v :=
  unique_continuous_linear_map_of_bilin ℝ B is_lax_milgram
#align
  is_coercive.unique_continuous_linear_equiv_of_bilin IsCoercive.unique_continuous_linear_equiv_of_bilin

end IsCoercive

