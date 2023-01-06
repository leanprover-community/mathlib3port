/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis

! This file was ported from Lean 3 source module analysis.inner_product_space.rayleigh
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Calculus
import Mathbin.Analysis.InnerProductSpace.Dual
import Mathbin.Analysis.InnerProductSpace.Adjoint
import Mathbin.Analysis.Calculus.LagrangeMultipliers
import Mathbin.LinearAlgebra.Eigenspace

/-!
# The Rayleigh quotient

The Rayleigh quotient of a self-adjoint operator `T` on an inner product space `E` is the function
`λ x, ⟪T x, x⟫ / ‖x‖ ^ 2`.

The main results of this file are `is_self_adjoint.has_eigenvector_of_is_max_on` and
`is_self_adjoint.has_eigenvector_of_is_min_on`, which state that if `E` is complete, and if the
Rayleigh quotient attains its global maximum/minimum over some sphere at the point `x₀`, then `x₀`
is an eigenvector of `T`, and the `supr`/`infi` of `λ x, ⟪T x, x⟫ / ‖x‖ ^ 2` is the corresponding
eigenvalue.

The corollaries `is_self_adjoint.has_eigenvalue_supr_of_finite_dimensional` and
`is_self_adjoint.has_eigenvalue_supr_of_finite_dimensional` state that if `E` is finite-dimensional
and nontrivial, then `T` has some (nonzero) eigenvectors with eigenvalue the `supr`/`infi` of
`λ x, ⟪T x, x⟫ / ‖x‖ ^ 2`.

## TODO

A slightly more elaborate corollary is that if `E` is complete and `T` is a compact operator, then
`T` has some (nonzero) eigenvector with eigenvalue either `⨆ x, ⟪T x, x⟫ / ‖x‖ ^ 2` or
`⨅ x, ⟪T x, x⟫ / ‖x‖ ^ 2` (not necessarily both).

-/


variable {𝕜 : Type _} [IsROrC 𝕜]

variable {E : Type _} [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

open Nnreal

open Module.EndCat Metric

namespace ContinuousLinearMap

variable (T : E →L[𝕜] E)

-- mathport name: exprrayleigh_quotient
local notation "rayleigh_quotient" => fun x : E => T.reApplyInnerSelf x / ‖(x : E)‖ ^ 2

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `rayleigh_smul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `E] [] ")")
        (Term.implicitBinder "{" [`c] [":" `𝕜] "}")
        (Term.explicitBinder "(" [`hc] [":" («term_≠_» `c "≠" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
           "rayleigh_quotient")
          [(Algebra.Group.Defs.«term_•_» `c " • " `x)])
         "="
         (Term.app
          (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
           "rayleigh_quotient")
          [`x]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Classical.«tacticBy_cases_:_» "by_cases" [`hx ":"] («term_=_» `x "=" (num "0")))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `c "‖") "≠" (num "0")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hc)] "]"] [])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "≠" (num "0")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])]))))))
           []
           (Tactic.fieldSimp
            "field_simp"
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `norm_smul)
               ","
               (Tactic.simpLemma [] [] `T.re_apply_inner_self_smul)]
              "]")]
            [])
           []
           (Mathlib.Tactic.RingNF.ring "ring")])))
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
         [(Classical.«tacticBy_cases_:_» "by_cases" [`hx ":"] («term_=_» `x "=" (num "0")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `c "‖") "≠" (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hc)] "]"] [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "≠" (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])]))))))
          []
          (Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma [] [] `norm_smul)
              ","
              (Tactic.simpLemma [] [] `T.re_apply_inner_self_smul)]
             "]")]
           [])
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp
       "field_simp"
       []
       []
       []
       [(Tactic.simpArgs
         "["
         [(Tactic.simpLemma [] [] `norm_smul)
          ","
          (Tactic.simpLemma [] [] `T.re_apply_inner_self_smul)]
         "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `T.re_apply_inner_self_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "≠" (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `c "‖") "≠" (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hc)] "]"] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hc)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hc)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `c "‖") "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `c "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`hx ":"] («term_=_» `x "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `x "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
         "rayleigh_quotient")
        [(Algebra.Group.Defs.«term_•_» `c " • " `x)])
       "="
       (Term.app
        (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
         "rayleigh_quotient")
        [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
        "rayleigh_quotient")
       [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
       "rayleigh_quotient")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient', expected 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient._@.Analysis.InnerProductSpace.Rayleigh._hyg.71'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  rayleigh_smul
  ( x : E ) { c : 𝕜 } ( hc : c ≠ 0 ) : rayleigh_quotient c • x = rayleigh_quotient x
  :=
    by
      by_cases hx : x = 0
        · simp [ hx ]
        have : ‖ c ‖ ≠ 0 := by simp [ hc ]
        have : ‖ x ‖ ≠ 0 := by simp [ hx ]
        field_simp [ norm_smul , T.re_apply_inner_self_smul ]
        ring
#align continuous_linear_map.rayleigh_smul ContinuousLinearMap.rayleigh_smul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `image_rayleigh_eq_image_rayleigh_sphere [])
      (Command.declSig
       [(Term.implicitBinder "{" [`r] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder "(" [`hr] [":" («term_<_» (num "0") "<" `r)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Data.Set.Image.term_''_
          (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
           "rayleigh_quotient")
          " '' "
          (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))
         "="
         (Set.Data.Set.Image.term_''_
          (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
           "rayleigh_quotient")
          " '' "
          (Term.app `sphere [(num "0") `r])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))]
            [])
           []
           (Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                   [":" («term_≠_» `x "≠" (num "0"))])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxT)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "≠" (num "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])]))))))
             []
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `c
                []
                [(Term.typeSpec ":" `𝕜)]
                ":="
                («term_*_»
                 (coeNotation
                  "↑"
                  («term_⁻¹» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "⁻¹"))
                 "*"
                 `r))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" («term_≠_» `c "≠" (num "0")))]
                ":="
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
                      [(Tactic.simpLemma [] [] `c)
                       ","
                       (Tactic.simpLemma [] [] `hx)
                       ","
                       (Tactic.simpLemma [] [] `hr.ne')]
                      "]"]
                     [])]))))))
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Algebra.Group.Defs.«term_•_» `c " • " `x) "," (Term.hole "_") "," (Term.hole "_")]
               "⟩"))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.fieldSimp
                "field_simp"
                []
                []
                []
                [(Tactic.simpArgs
                  "["
                  [(Tactic.simpLemma [] [] `norm_smul)
                   ","
                   (Tactic.simpLemma [] [] `IsROrC.norm_eq_abs)
                   ","
                   (Tactic.simpLemma [] [] (Term.app `abs_of_nonneg [`hr.le]))]
                  "]")]
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `T.rayleigh_smul [`x `this]))]
                 "]")
                [])
               []
               (Tactic.exact "exact" `hxT)])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxT)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [`x
                ","
                (Term.app
                 `ne_zero_of_mem_sphere
                 [`hr.ne' (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
                ","
                `hxT]
               "⟩"))])])))
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
         [(Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))]
           [])
          []
          (Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                  [":" («term_≠_» `x "≠" (num "0"))])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxT)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "≠" (num "0")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])]))))))
            []
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `c
               []
               [(Term.typeSpec ":" `𝕜)]
               ":="
               («term_*_»
                (coeNotation
                 "↑"
                 («term_⁻¹» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "⁻¹"))
                "*"
                `r))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" («term_≠_» `c "≠" (num "0")))]
               ":="
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
                     [(Tactic.simpLemma [] [] `c)
                      ","
                      (Tactic.simpLemma [] [] `hx)
                      ","
                      (Tactic.simpLemma [] [] `hr.ne')]
                     "]"]
                    [])]))))))
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Algebra.Group.Defs.«term_•_» `c " • " `x) "," (Term.hole "_") "," (Term.hole "_")]
              "⟩"))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.fieldSimp
               "field_simp"
               []
               []
               []
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `norm_smul)
                  ","
                  (Tactic.simpLemma [] [] `IsROrC.norm_eq_abs)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `abs_of_nonneg [`hr.le]))]
                 "]")]
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `T.rayleigh_smul [`x `this]))]
                "]")
               [])
              []
              (Tactic.exact "exact" `hxT)])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxT)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [`x
               ","
               (Term.app `ne_zero_of_mem_sphere [`hr.ne' (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
               ","
               `hxT]
              "⟩"))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxT)])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [`x
           ","
           (Term.app `ne_zero_of_mem_sphere [`hr.ne' (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
           ","
           `hxT]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`x
         ","
         (Term.app `ne_zero_of_mem_sphere [`hr.ne' (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
         ","
         `hxT]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`x
        ","
        (Term.app `ne_zero_of_mem_sphere [`hr.ne' (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
        ","
        `hxT]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxT
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_zero_of_mem_sphere [`hr.ne' (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `hr.ne'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_zero_of_mem_sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxT)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
              [":" («term_≠_» `x "≠" (num "0"))])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxT)])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "≠" (num "0")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])]))))))
        []
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `c
           []
           [(Term.typeSpec ":" `𝕜)]
           ":="
           («term_*_»
            (coeNotation "↑" («term_⁻¹» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "⁻¹"))
            "*"
            `r))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" («term_≠_» `c "≠" (num "0")))]
           ":="
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
                 [(Tactic.simpLemma [] [] `c)
                  ","
                  (Tactic.simpLemma [] [] `hx)
                  ","
                  (Tactic.simpLemma [] [] `hr.ne')]
                 "]"]
                [])]))))))
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Algebra.Group.Defs.«term_•_» `c " • " `x) "," (Term.hole "_") "," (Term.hole "_")]
          "⟩"))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma [] [] `norm_smul)
              ","
              (Tactic.simpLemma [] [] `IsROrC.norm_eq_abs)
              ","
              (Tactic.simpLemma [] [] (Term.app `abs_of_nonneg [`hr.le]))]
             "]")]
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `T.rayleigh_smul [`x `this]))] "]")
           [])
          []
          (Tactic.exact "exact" `hxT)])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `T.rayleigh_smul [`x `this]))] "]")
         [])
        []
        (Tactic.exact "exact" `hxT)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `hxT)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxT
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `T.rayleigh_smul [`x `this]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `T.rayleigh_smul [`x `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T.rayleigh_smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.fieldSimp
         "field_simp"
         []
         []
         []
         [(Tactic.simpArgs
           "["
           [(Tactic.simpLemma [] [] `norm_smul)
            ","
            (Tactic.simpLemma [] [] `IsROrC.norm_eq_abs)
            ","
            (Tactic.simpLemma [] [] (Term.app `abs_of_nonneg [`hr.le]))]
           "]")]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp
       "field_simp"
       []
       []
       []
       [(Tactic.simpArgs
         "["
         [(Tactic.simpLemma [] [] `norm_smul)
          ","
          (Tactic.simpLemma [] [] `IsROrC.norm_eq_abs)
          ","
          (Tactic.simpLemma [] [] (Term.app `abs_of_nonneg [`hr.le]))]
         "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_of_nonneg [`hr.le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr.le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_of_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsROrC.norm_eq_abs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Algebra.Group.Defs.«term_•_» `c " • " `x) "," (Term.hole "_") "," (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Algebra.Group.Defs.«term_•_» `c " • " `x) "," (Term.hole "_") "," (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `c " • " `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_≠_» `c "≠" (num "0")))]
         ":="
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
               [(Tactic.simpLemma [] [] `c)
                ","
                (Tactic.simpLemma [] [] `hx)
                ","
                (Tactic.simpLemma [] [] `hr.ne')]
               "]"]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
            [(Tactic.simpLemma [] [] `c)
             ","
             (Tactic.simpLemma [] [] `hx)
             ","
             (Tactic.simpLemma [] [] `hr.ne')]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `c)
         ","
         (Tactic.simpLemma [] [] `hx)
         ","
         (Tactic.simpLemma [] [] `hr.ne')]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr.ne'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `c "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `c
         []
         [(Term.typeSpec ":" `𝕜)]
         ":="
         («term_*_»
          (coeNotation "↑" («term_⁻¹» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "⁻¹"))
          "*"
          `r))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (coeNotation "↑" («term_⁻¹» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "⁻¹"))
       "*"
       `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (coeNotation "↑" («term_⁻¹» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (some 1024, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "≠" (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖") "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
            [":" («term_≠_» `x "≠" (num "0"))])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxT)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `x "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Data.Set.Image.term_''_
        (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
         "rayleigh_quotient")
        " '' "
        (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))
       "="
       (Set.Data.Set.Image.term_''_
        (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
         "rayleigh_quotient")
        " '' "
        (Term.app `sphere [(num "0") `r])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
        "rayleigh_quotient")
       " '' "
       (Term.app `sphere [(num "0") `r]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sphere [(num "0") `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
       "rayleigh_quotient")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient', expected 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient._@.Analysis.InnerProductSpace.Rayleigh._hyg.71'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  image_rayleigh_eq_image_rayleigh_sphere
  { r : ℝ } ( hr : 0 < r ) : rayleigh_quotient '' { 0 } ᶜ = rayleigh_quotient '' sphere 0 r
  :=
    by
      ext a
        constructor
        ·
          rintro ⟨ x , hx : x ≠ 0 , hxT ⟩
            have : ‖ x ‖ ≠ 0 := by simp [ hx ]
            let c : 𝕜 := ↑ ‖ x ‖ ⁻¹ * r
            have : c ≠ 0 := by simp [ c , hx , hr.ne' ]
            refine' ⟨ c • x , _ , _ ⟩
            · field_simp [ norm_smul , IsROrC.norm_eq_abs , abs_of_nonneg hr.le ]
            · rw [ T.rayleigh_smul x this ] exact hxT
        · rintro ⟨ x , hx , hxT ⟩ exact ⟨ x , ne_zero_of_mem_sphere hr.ne' ⟨ x , hx ⟩ , hxT ⟩
#align
  continuous_linear_map.image_rayleigh_eq_image_rayleigh_sphere ContinuousLinearMap.image_rayleigh_eq_image_rayleigh_sphere

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `supr_rayleigh_eq_supr_rayleigh_sphere [])
      (Command.declSig
       [(Term.implicitBinder "{" [`r] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder "(" [`hr] [":" («term_<_» (num "0") "<" `r)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Order.CompleteLattice.«term⨆_,_»
          "⨆"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
          ", "
          (Term.app
           (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
            "rayleigh_quotient")
           [`x]))
         "="
         (Order.CompleteLattice.«term⨆_,_»
          "⨆"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group ":" (Term.app `sphere [(Term.typeAscription "(" (num "0") ":" [`E] ")") `r]))]))
          ", "
          (Term.app
           (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
            "rayleigh_quotient")
           [`x])))))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        («term_=_»
         (Order.CompleteLattice.«term⨆_,_»
          "⨆"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group
              ":"
              (Order.Basic.«term_ᶜ»
               (Term.typeAscription
                "("
                («term{_}» "{" [(num "0")] "}")
                ":"
                [(Term.app `Set [`E])]
                ")")
               "ᶜ"))]))
          ", "
          (Term.app
           (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
            "rayleigh_quotient")
           [`x]))
         "="
         (Term.hole "_"))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.explicit "@" `supₛ_image')
                 [(Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
                   "rayleigh_quotient")]))
               ","
               (Tactic.simpLemma [] [] (Term.app `T.image_rayleigh_eq_image_rayleigh_sphere [`hr]))]
              "]"]
             [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Order.CompleteLattice.«term⨆_,_»
         "⨆"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder
           (Lean.binderIdent `x)
           [(group
             ":"
             (Order.Basic.«term_ᶜ»
              (Term.typeAscription
               "("
               («term{_}» "{" [(num "0")] "}")
               ":"
               [(Term.app `Set [`E])]
               ")")
              "ᶜ"))]))
         ", "
         (Term.app
          (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
           "rayleigh_quotient")
          [`x]))
        "="
        (Term.hole "_"))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma
               []
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                (Term.explicit "@" `supₛ_image')
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
                  "rayleigh_quotient")]))
              ","
              (Tactic.simpLemma [] [] (Term.app `T.image_rayleigh_eq_image_rayleigh_sphere [`hr]))]
             "]"]
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma
          []
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           (Term.explicit "@" `supₛ_image')
           [(Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
             "rayleigh_quotient")]))
         ","
         (Tactic.simpLemma [] [] (Term.app `T.image_rayleigh_eq_image_rayleigh_sphere [`hr]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `T.image_rayleigh_eq_image_rayleigh_sphere [`hr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T.image_rayleigh_eq_image_rayleigh_sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `supₛ_image')
       [(Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
         "rayleigh_quotient")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
       "rayleigh_quotient")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient', expected 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient._@.Analysis.InnerProductSpace.Rayleigh._hyg.71'
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
  supr_rayleigh_eq_supr_rayleigh_sphere
  { r : ℝ } ( hr : 0 < r )
    :
      ⨆ x : { x : E // x ≠ 0 } , rayleigh_quotient x
        =
        ⨆ x : sphere ( 0 : E ) r , rayleigh_quotient x
  :=
    show
      ⨆ x : ( { 0 } : Set E ) ᶜ , rayleigh_quotient x = _
      by
        simp
          only
          [
            ← @ supₛ_image' _ _ _ _ rayleigh_quotient , T.image_rayleigh_eq_image_rayleigh_sphere hr
            ]
#align
  continuous_linear_map.supr_rayleigh_eq_supr_rayleigh_sphere ContinuousLinearMap.supr_rayleigh_eq_supr_rayleigh_sphere

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `infi_rayleigh_eq_infi_rayleigh_sphere [])
      (Command.declSig
       [(Term.implicitBinder "{" [`r] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder "(" [`hr] [":" («term_<_» (num "0") "<" `r)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Order.CompleteLattice.«term⨅_,_»
          "⨅"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
          ", "
          (Term.app
           (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
            "rayleigh_quotient")
           [`x]))
         "="
         (Order.CompleteLattice.«term⨅_,_»
          "⨅"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group ":" (Term.app `sphere [(Term.typeAscription "(" (num "0") ":" [`E] ")") `r]))]))
          ", "
          (Term.app
           (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
            "rayleigh_quotient")
           [`x])))))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        («term_=_»
         (Order.CompleteLattice.«term⨅_,_»
          "⨅"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group
              ":"
              (Order.Basic.«term_ᶜ»
               (Term.typeAscription
                "("
                («term{_}» "{" [(num "0")] "}")
                ":"
                [(Term.app `Set [`E])]
                ")")
               "ᶜ"))]))
          ", "
          (Term.app
           (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
            "rayleigh_quotient")
           [`x]))
         "="
         (Term.hole "_"))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.explicit "@" `infₛ_image')
                 [(Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
                   "rayleigh_quotient")]))
               ","
               (Tactic.simpLemma [] [] (Term.app `T.image_rayleigh_eq_image_rayleigh_sphere [`hr]))]
              "]"]
             [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Order.CompleteLattice.«term⨅_,_»
         "⨅"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder
           (Lean.binderIdent `x)
           [(group
             ":"
             (Order.Basic.«term_ᶜ»
              (Term.typeAscription
               "("
               («term{_}» "{" [(num "0")] "}")
               ":"
               [(Term.app `Set [`E])]
               ")")
              "ᶜ"))]))
         ", "
         (Term.app
          (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
           "rayleigh_quotient")
          [`x]))
        "="
        (Term.hole "_"))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma
               []
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                (Term.explicit "@" `infₛ_image')
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
                  "rayleigh_quotient")]))
              ","
              (Tactic.simpLemma [] [] (Term.app `T.image_rayleigh_eq_image_rayleigh_sphere [`hr]))]
             "]"]
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma
          []
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           (Term.explicit "@" `infₛ_image')
           [(Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
             "rayleigh_quotient")]))
         ","
         (Tactic.simpLemma [] [] (Term.app `T.image_rayleigh_eq_image_rayleigh_sphere [`hr]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `T.image_rayleigh_eq_image_rayleigh_sphere [`hr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T.image_rayleigh_eq_image_rayleigh_sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `infₛ_image')
       [(Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
         "rayleigh_quotient")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
       "rayleigh_quotient")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient', expected 'ContinuousLinearMap.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient._@.Analysis.InnerProductSpace.Rayleigh._hyg.71'
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
  infi_rayleigh_eq_infi_rayleigh_sphere
  { r : ℝ } ( hr : 0 < r )
    :
      ⨅ x : { x : E // x ≠ 0 } , rayleigh_quotient x
        =
        ⨅ x : sphere ( 0 : E ) r , rayleigh_quotient x
  :=
    show
      ⨅ x : ( { 0 } : Set E ) ᶜ , rayleigh_quotient x = _
      by
        simp
          only
          [
            ← @ infₛ_image' _ _ _ _ rayleigh_quotient , T.image_rayleigh_eq_image_rayleigh_sphere hr
            ]
#align
  continuous_linear_map.infi_rayleigh_eq_infi_rayleigh_sphere ContinuousLinearMap.infi_rayleigh_eq_infi_rayleigh_sphere

end ContinuousLinearMap

namespace IsSelfAdjoint

section Real

variable {F : Type _} [InnerProductSpace ℝ F]

theorem LinearMap.IsSymmetric.hasStrictFderivAtReApplyInnerSelf {T : F →L[ℝ] F}
    (hT : (T : F →ₗ[ℝ] F).IsSymmetric) (x₀ : F) :
    HasStrictFderivAt T.reApplyInnerSelf (bit0 (innerSL (T x₀) : F →L[ℝ] ℝ)) x₀ :=
  by
  convert T.has_strict_fderiv_at.inner (hasStrictFderivAtId x₀)
  ext y
  simp_rw [_root_.bit0, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    innerSL_apply, fderiv_inner_clm_apply, id.def, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, hT.apply_clm x₀ y, real_inner_comm _ x₀]
#align
  linear_map.is_symmetric.has_strict_fderiv_at_re_apply_inner_self LinearMap.IsSymmetric.hasStrictFderivAtReApplyInnerSelf

variable [CompleteSpace F] {T : F →L[ℝ] F}

-- mathport name: exprrayleigh_quotient
local notation "rayleigh_quotient" => fun x : F => T.reApplyInnerSelf x / ‖(x : F)‖ ^ 2

theorem linearly_dependent_of_is_local_extr_on (hT : IsSelfAdjoint T) {x₀ : F}
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : F) ‖x₀‖) x₀) :
    ∃ a b : ℝ, (a, b) ≠ 0 ∧ a • x₀ + b • T x₀ = 0 :=
  by
  have H : IsLocalExtrOn T.re_apply_inner_self { x : F | ‖x‖ ^ 2 = ‖x₀‖ ^ 2 } x₀ :=
    by
    convert hextr
    ext x
    simp [dist_eq_norm]
  -- find Lagrange multipliers for the function `T.re_apply_inner_self` and the
  -- hypersurface-defining function `λ x, ‖x‖ ^ 2`
  obtain ⟨a, b, h₁, h₂⟩ :=
    IsLocalExtrOn.exists_multipliers_of_has_strict_fderiv_at_1d H (hasStrictFderivAtNormSq x₀)
      (hT.is_symmetric.has_strict_fderiv_at_re_apply_inner_self x₀)
  refine' ⟨a, b, h₁, _⟩
  apply (InnerProductSpace.toDualMap ℝ F).Injective
  simp only [LinearIsometry.map_add, LinearIsometry.map_smul, LinearIsometry.map_zero]
  change a • innerSL x₀ + b • innerSL (T x₀) = 0
  apply smul_right_injective (F →L[ℝ] ℝ) (two_ne_zero : (2 : ℝ) ≠ 0)
  simpa only [_root_.bit0, add_smul, smul_add, one_smul, add_zero] using h₂
#align
  is_self_adjoint.linearly_dependent_of_is_local_extr_on IsSelfAdjoint.linearly_dependent_of_is_local_extr_on

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `eq_smul_self_of_is_local_extr_on_real [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hT] [":" (Term.app `IsSelfAdjoint [`T])] [] ")")
        (Term.implicitBinder "{" [`x₀] [":" `F] "}")
        (Term.explicitBinder
         "("
         [`hextr]
         [":"
          (Term.app
           `IsLocalExtrOn
           [(Term.proj `T "." `reApplyInnerSelf)
            (Term.app
             `sphere
             [(Term.typeAscription "(" (num "0") ":" [`F] ")")
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
            `x₀])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `T [`x₀])
         "="
         (Algebra.Group.Defs.«term_•_»
          (Term.app
           (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
            "rayleigh_quotient")
           [`x₀])
          " • "
          `x₀))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₂)])
                  [])]
                "⟩")])]
            []
            [":=" [(Term.app `hT.linearly_dependent_of_is_local_extr_on [`hextr])]])
           []
           (Classical.«tacticBy_cases_:_» "by_cases" [`hx₀ ":"] («term_=_» `x₀ "=" (num "0")))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])])
           []
           (Classical.«tacticBy_cases_:_» "by_cases" [`hb ":"] («term_=_» `b "=" (num "0")))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" («term_≠_» `a "≠" (num "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.Simpa.simpa
                     "simpa"
                     []
                     []
                     (Std.Tactic.Simpa.simpaArgsRest
                      []
                      []
                      []
                      [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb)] "]")]
                      ["using" `h₁]))]))))))
             []
             (Tactic.refine' "refine'" (Term.app `absurd [(Term.hole "_") `hx₀]))
             []
             (Tactic.apply "apply" (Term.app `smul_right_injective [`F `this]))
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb)] "]")]
               ["using" `h₂]))])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `c
              []
              [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
              ":="
              («term_*_» («term-_» "-" («term_⁻¹» `b "⁻¹")) "*" `a))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hc []]
              [(Term.typeSpec
                ":"
                («term_=_» (Term.app `T [`x₀]) "=" (Algebra.Group.Defs.«term_•_» `c " • " `x₀)))]
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
                       («term_=_»
                        («term_*_» `b "*" («term_*_» («term_⁻¹» `b "⁻¹") "*" `a))
                        "="
                        `a))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.fieldSimp
                          "field_simp"
                          []
                          []
                          []
                          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `mul_comm)] "]")]
                          [])]))))))
                  []
                  (Tactic.apply "apply" (Term.app `smul_right_injective [`F `hb]))
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   []
                   ["["
                    [(Tactic.simpLemma [] [] `c)
                     ","
                     (Tactic.simpLemma [] [] (Term.app `eq_neg_of_add_eq_zero_left [`h₂]))
                     ","
                     (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                     ","
                     (Tactic.simpLemma [] [] `this)]
                    "]"]
                   [])]))))))
           []
           (convert "convert" [] `hc [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])]))))))
           []
           (Tactic.fieldSimp "field_simp" [] [] [] [] [])
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
               [(Tactic.simpLemma [] [] `inner_smul_left)
                ","
                (Tactic.simpLemma [] [] `real_inner_self_eq_norm_mul_norm)
                ","
                (Tactic.simpLemma [] [] `sq)]
               "]")]
             ["using"
              (Term.app
               `congr_arg
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`x]
                  []
                  "=>"
                  (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ» "⟪" `x ", " `x₀ "⟫_ℝ")))
                `hc])]))])))
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
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₁)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₂)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app `hT.linearly_dependent_of_is_local_extr_on [`hextr])]])
          []
          (Classical.«tacticBy_cases_:_» "by_cases" [`hx₀ ":"] («term_=_» `x₀ "=" (num "0")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])])
          []
          (Classical.«tacticBy_cases_:_» "by_cases" [`hb ":"] («term_=_» `b "=" (num "0")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" («term_≠_» `a "≠" (num "0")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.Simpa.simpa
                    "simpa"
                    []
                    []
                    (Std.Tactic.Simpa.simpaArgsRest
                     []
                     []
                     []
                     [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb)] "]")]
                     ["using" `h₁]))]))))))
            []
            (Tactic.refine' "refine'" (Term.app `absurd [(Term.hole "_") `hx₀]))
            []
            (Tactic.apply "apply" (Term.app `smul_right_injective [`F `this]))
            []
            (Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb)] "]")]
              ["using" `h₂]))])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `c
             []
             [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
             ":="
             («term_*_» («term-_» "-" («term_⁻¹» `b "⁻¹")) "*" `a))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hc []]
             [(Term.typeSpec
               ":"
               («term_=_» (Term.app `T [`x₀]) "=" (Algebra.Group.Defs.«term_•_» `c " • " `x₀)))]
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
                      («term_=_» («term_*_» `b "*" («term_*_» («term_⁻¹» `b "⁻¹") "*" `a)) "=" `a))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.fieldSimp
                         "field_simp"
                         []
                         []
                         []
                         [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `mul_comm)] "]")]
                         [])]))))))
                 []
                 (Tactic.apply "apply" (Term.app `smul_right_injective [`F `hb]))
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma [] [] `c)
                    ","
                    (Tactic.simpLemma [] [] (Term.app `eq_neg_of_add_eq_zero_left [`h₂]))
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                    ","
                    (Tactic.simpLemma [] [] `this)]
                   "]"]
                  [])]))))))
          []
          (convert "convert" [] `hc [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])]))))))
          []
          (Tactic.fieldSimp "field_simp" [] [] [] [] [])
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
              [(Tactic.simpLemma [] [] `inner_smul_left)
               ","
               (Tactic.simpLemma [] [] `real_inner_self_eq_norm_mul_norm)
               ","
               (Tactic.simpLemma [] [] `sq)]
              "]")]
            ["using"
             (Term.app
              `congr_arg
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ» "⟪" `x ", " `x₀ "⟫_ℝ")))
               `hc])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
          [(Tactic.simpLemma [] [] `inner_smul_left)
           ","
           (Tactic.simpLemma [] [] `real_inner_self_eq_norm_mul_norm)
           ","
           (Tactic.simpLemma [] [] `sq)]
          "]")]
        ["using"
         (Term.app
          `congr_arg
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ» "⟪" `x ", " `x₀ "⟫_ℝ")))
           `hc])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ» "⟪" `x ", " `x₀ "⟫_ℝ")))
        `hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ» "⟪" `x ", " `x₀ "⟫_ℝ")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ» "⟪" `x ", " `x₀ "⟫_ℝ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`x]
       []
       "=>"
       (Analysis.InnerProductSpace.Basic.«term⟪_,_⟫_ℝ» "⟪" `x ", " `x₀ "⟫_ℝ")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_self_eq_norm_mul_norm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_smul_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp "field_simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `hc [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hc []]
         [(Term.typeSpec
           ":"
           («term_=_» (Term.app `T [`x₀]) "=" (Algebra.Group.Defs.«term_•_» `c " • " `x₀)))]
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
                  («term_=_» («term_*_» `b "*" («term_*_» («term_⁻¹» `b "⁻¹") "*" `a)) "=" `a))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.fieldSimp
                     "field_simp"
                     []
                     []
                     []
                     [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `mul_comm)] "]")]
                     [])]))))))
             []
             (Tactic.apply "apply" (Term.app `smul_right_injective [`F `hb]))
             []
             (Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `c)
                ","
                (Tactic.simpLemma [] [] (Term.app `eq_neg_of_add_eq_zero_left [`h₂]))
                ","
                (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                ","
                (Tactic.simpLemma [] [] `this)]
               "]"]
              [])]))))))
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
               («term_=_» («term_*_» `b "*" («term_*_» («term_⁻¹» `b "⁻¹") "*" `a)) "=" `a))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.fieldSimp
                  "field_simp"
                  []
                  []
                  []
                  [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `mul_comm)] "]")]
                  [])]))))))
          []
          (Tactic.apply "apply" (Term.app `smul_right_injective [`F `hb]))
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `c)
             ","
             (Tactic.simpLemma [] [] (Term.app `eq_neg_of_add_eq_zero_left [`h₂]))
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
             ","
             (Tactic.simpLemma [] [] `this)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `c)
         ","
         (Tactic.simpLemma [] [] (Term.app `eq_neg_of_add_eq_zero_left [`h₂]))
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
         ","
         (Tactic.simpLemma [] [] `this)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_neg_of_add_eq_zero_left [`h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_neg_of_add_eq_zero_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `smul_right_injective [`F `hb]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smul_right_injective [`F `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smul_right_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_» («term_*_» `b "*" («term_*_» («term_⁻¹» `b "⁻¹") "*" `a)) "=" `a))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.fieldSimp
              "field_simp"
              []
              []
              []
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `mul_comm)] "]")]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `mul_comm)] "]")]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp
       "field_simp"
       []
       []
       []
       [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `mul_comm)] "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» («term_*_» `b "*" («term_*_» («term_⁻¹» `b "⁻¹") "*" `a)) "=" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» `b "*" («term_*_» («term_⁻¹» `b "⁻¹") "*" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_⁻¹» `b "⁻¹") "*" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_⁻¹» `b "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» («term_⁻¹» `b "⁻¹") "*" `a)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `T [`x₀]) "=" (Algebra.Group.Defs.«term_•_» `c " • " `x₀))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `c " • " `x₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `T [`x₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `c
         []
         [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
         ":="
         («term_*_» («term-_» "-" («term_⁻¹» `b "⁻¹")) "*" `a))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term-_» "-" («term_⁻¹» `b "⁻¹")) "*" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term-_» "-" («term_⁻¹» `b "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» `b "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 75, (some 75, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" («term_≠_» `a "≠" (num "0")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 []
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb)] "]")]
                 ["using" `h₁]))]))))))
        []
        (Tactic.refine' "refine'" (Term.app `absurd [(Term.hole "_") `hx₀]))
        []
        (Tactic.apply "apply" (Term.app `smul_right_injective [`F `this]))
        []
        (Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          []
          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb)] "]")]
          ["using" `h₂]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb)] "]")]
        ["using" `h₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `smul_right_injective [`F `this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smul_right_injective [`F `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smul_right_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `absurd [(Term.hole "_") `hx₀]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `absurd [(Term.hole "_") `hx₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `absurd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_≠_» `a "≠" (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb)] "]")]
               ["using" `h₁]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb)] "]")]
            ["using" `h₁]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hb)] "]")]
        ["using" `h₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `a "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`hb ":"] («term_=_» `b "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `b "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`hx₀ ":"] («term_=_» `x₀ "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `x₀ "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₁)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₂)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `hT.linearly_dependent_of_is_local_extr_on [`hextr])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hT.linearly_dependent_of_is_local_extr_on [`hextr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hextr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hT.linearly_dependent_of_is_local_extr_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `T [`x₀])
       "="
       (Algebra.Group.Defs.«term_•_»
        (Term.app
         (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
          "rayleigh_quotient")
         [`x₀])
        " • "
        `x₀))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.app
        (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient
         "rayleigh_quotient")
        [`x₀])
       " • "
       `x₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.app
       (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient "rayleigh_quotient")
       [`x₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient "rayleigh_quotient")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient', expected 'IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient._@.Analysis.InnerProductSpace.Rayleigh._hyg.113'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  eq_smul_self_of_is_local_extr_on_real
  ( hT : IsSelfAdjoint T )
      { x₀ : F }
      ( hextr : IsLocalExtrOn T . reApplyInnerSelf sphere ( 0 : F ) ‖ x₀ ‖ x₀ )
    : T x₀ = rayleigh_quotient x₀ • x₀
  :=
    by
      obtain ⟨ a , b , h₁ , h₂ ⟩ := hT.linearly_dependent_of_is_local_extr_on hextr
        by_cases hx₀ : x₀ = 0
        · simp [ hx₀ ]
        by_cases hb : b = 0
        ·
          have : a ≠ 0 := by simpa [ hb ] using h₁
            refine' absurd _ hx₀
            apply smul_right_injective F this
            simpa [ hb ] using h₂
        let c : ℝ := - b ⁻¹ * a
        have
          hc
            : T x₀ = c • x₀
            :=
            by
              have : b * b ⁻¹ * a = a := by field_simp [ mul_comm ]
                apply smul_right_injective F hb
                simp [ c , eq_neg_of_add_eq_zero_left h₂ , ← mul_smul , this ]
        convert hc
        have : ‖ x₀ ‖ ≠ 0 := by simp [ hx₀ ]
        field_simp
        simpa
          [ inner_smul_left , real_inner_self_eq_norm_mul_norm , sq ]
            using congr_arg fun x => ⟪ x , x₀ ⟫_ℝ hc
#align
  is_self_adjoint.eq_smul_self_of_is_local_extr_on_real IsSelfAdjoint.eq_smul_self_of_is_local_extr_on_real

end Real

section CompleteSpace

variable [CompleteSpace E] {T : E →L[𝕜] E}

-- mathport name: exprrayleigh_quotient
local notation "rayleigh_quotient" => fun x : E => T.reApplyInnerSelf x / ‖(x : E)‖ ^ 2

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `eq_smul_self_of_is_local_extr_on [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hT] [":" (Term.app `IsSelfAdjoint [`T])] [] ")")
        (Term.implicitBinder "{" [`x₀] [":" `E] "}")
        (Term.explicitBinder
         "("
         [`hextr]
         [":"
          (Term.app
           `IsLocalExtrOn
           [(Term.proj `T "." `reApplyInnerSelf)
            (Term.app
             `sphere
             [(Term.typeAscription "(" (num "0") ":" [`E] ")")
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
            `x₀])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `T [`x₀])
         "="
         (Algebra.Group.Defs.«term_•_»
          (Term.typeAscription
           "("
           (coeNotation
            "↑"
            (Term.app
             (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
              "rayleigh_quotient")
             [`x₀]))
           ":"
           [`𝕜]
           ")")
          " • "
          `x₀))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticLetI_
            "letI"
            (Term.haveDecl
             (Term.haveIdDecl [] [] ":=" (Term.app `InnerProductSpace.isROrCToReal [`𝕜 `E]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `hSA
              []
              []
              ":="
              `hT.is_symmetric.restrict_scalars.to_self_adjoint.prop)))
           []
           (Tactic.exact "exact" (Term.app `hSA.eq_smul_self_of_is_local_extr_on_real [`hextr]))])))
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
         [(Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl [] [] ":=" (Term.app `InnerProductSpace.isROrCToReal [`𝕜 `E]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `hSA
             []
             []
             ":="
             `hT.is_symmetric.restrict_scalars.to_self_adjoint.prop)))
          []
          (Tactic.exact "exact" (Term.app `hSA.eq_smul_self_of_is_local_extr_on_real [`hextr]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hSA.eq_smul_self_of_is_local_extr_on_real [`hextr]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hSA.eq_smul_self_of_is_local_extr_on_real [`hextr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hextr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hSA.eq_smul_self_of_is_local_extr_on_real
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl `hSA [] [] ":=" `hT.is_symmetric.restrict_scalars.to_self_adjoint.prop)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hT.is_symmetric.restrict_scalars.to_self_adjoint.prop
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticLetI_
       "letI"
       (Term.haveDecl
        (Term.haveIdDecl [] [] ":=" (Term.app `InnerProductSpace.isROrCToReal [`𝕜 `E]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `InnerProductSpace.isROrCToReal [`𝕜 `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `InnerProductSpace.isROrCToReal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `T [`x₀])
       "="
       (Algebra.Group.Defs.«term_•_»
        (Term.typeAscription
         "("
         (coeNotation
          "↑"
          (Term.app
           (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
            "rayleigh_quotient")
           [`x₀]))
         ":"
         [`𝕜]
         ")")
        " • "
        `x₀))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.typeAscription
        "("
        (coeNotation
         "↑"
         (Term.app
          (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
           "rayleigh_quotient")
          [`x₀]))
        ":"
        [`𝕜]
        ")")
       " • "
       `x₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.typeAscription
       "("
       (coeNotation
        "↑"
        (Term.app
         (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
          "rayleigh_quotient")
         [`x₀]))
       ":"
       [`𝕜]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation
       "↑"
       (Term.app
        (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
         "rayleigh_quotient")
        [`x₀]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
        "rayleigh_quotient")
       [`x₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
       "rayleigh_quotient")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1', expected 'IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1._@.Analysis.InnerProductSpace.Rayleigh._hyg.154'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  eq_smul_self_of_is_local_extr_on
  ( hT : IsSelfAdjoint T )
      { x₀ : E }
      ( hextr : IsLocalExtrOn T . reApplyInnerSelf sphere ( 0 : E ) ‖ x₀ ‖ x₀ )
    : T x₀ = ( ↑ rayleigh_quotient x₀ : 𝕜 ) • x₀
  :=
    by
      letI := InnerProductSpace.isROrCToReal 𝕜 E
        let hSA := hT.is_symmetric.restrict_scalars.to_self_adjoint.prop
        exact hSA.eq_smul_self_of_is_local_extr_on_real hextr
#align
  is_self_adjoint.eq_smul_self_of_is_local_extr_on IsSelfAdjoint.eq_smul_self_of_is_local_extr_on

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For a self-adjoint operator `T`, a local extremum of the Rayleigh quotient of `T` on a sphere\ncentred at the origin is an eigenvector of `T`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `has_eigenvector_of_is_local_extr_on [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hT] [":" (Term.app `IsSelfAdjoint [`T])] [] ")")
        (Term.implicitBinder "{" [`x₀] [":" `E] "}")
        (Term.explicitBinder "(" [`hx₀] [":" («term_≠_» `x₀ "≠" (num "0"))] [] ")")
        (Term.explicitBinder
         "("
         [`hextr]
         [":"
          (Term.app
           `IsLocalExtrOn
           [(Term.proj `T "." `reApplyInnerSelf)
            (Term.app
             `sphere
             [(Term.typeAscription "(" (num "0") ":" [`E] ")")
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
            `x₀])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasEigenvector
         [(Term.typeAscription
           "("
           `T
           ":"
           [(Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
           ")")
          (coeNotation
           "↑"
           (Term.app
            (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
             "rayleigh_quotient")
            [`x₀]))
          `x₀])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `hx₀] "⟩"))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Module.EndCat.mem_eigenspace_iff)] "]")
            [])
           []
           (Tactic.exact "exact" (Term.app `hT.eq_smul_self_of_is_local_extr_on [`hextr]))])))
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
         [(Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `hx₀] "⟩"))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Module.EndCat.mem_eigenspace_iff)] "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `hT.eq_smul_self_of_is_local_extr_on [`hextr]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hT.eq_smul_self_of_is_local_extr_on [`hextr]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hT.eq_smul_self_of_is_local_extr_on [`hextr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hextr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hT.eq_smul_self_of_is_local_extr_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Module.EndCat.mem_eigenspace_iff)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Module.EndCat.mem_eigenspace_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [(Term.hole "_") "," `hx₀] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `hx₀] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasEigenvector
       [(Term.typeAscription
         "("
         `T
         ":"
         [(Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
         ")")
        (coeNotation
         "↑"
         (Term.app
          (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
           "rayleigh_quotient")
          [`x₀]))
        `x₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (coeNotation
       "↑"
       (Term.app
        (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
         "rayleigh_quotient")
        [`x₀]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
        "rayleigh_quotient")
       [`x₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
       "rayleigh_quotient")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1', expected 'IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1._@.Analysis.InnerProductSpace.Rayleigh._hyg.154'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    For a self-adjoint operator `T`, a local extremum of the Rayleigh quotient of `T` on a sphere
    centred at the origin is an eigenvector of `T`. -/
  theorem
    has_eigenvector_of_is_local_extr_on
    ( hT : IsSelfAdjoint T )
        { x₀ : E }
        ( hx₀ : x₀ ≠ 0 )
        ( hextr : IsLocalExtrOn T . reApplyInnerSelf sphere ( 0 : E ) ‖ x₀ ‖ x₀ )
      : HasEigenvector ( T : E →ₗ[ 𝕜 ] E ) ↑ rayleigh_quotient x₀ x₀
    :=
      by
        refine' ⟨ _ , hx₀ ⟩
          rw [ Module.EndCat.mem_eigenspace_iff ]
          exact hT.eq_smul_self_of_is_local_extr_on hextr
#align
  is_self_adjoint.has_eigenvector_of_is_local_extr_on IsSelfAdjoint.has_eigenvector_of_is_local_extr_on

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For a self-adjoint operator `T`, a maximum of the Rayleigh quotient of `T` on a sphere centred\nat the origin is an eigenvector of `T`, with eigenvalue the global supremum of the Rayleigh\nquotient. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `has_eigenvector_of_is_max_on [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hT] [":" (Term.app `IsSelfAdjoint [`T])] [] ")")
        (Term.implicitBinder "{" [`x₀] [":" `E] "}")
        (Term.explicitBinder "(" [`hx₀] [":" («term_≠_» `x₀ "≠" (num "0"))] [] ")")
        (Term.explicitBinder
         "("
         [`hextr]
         [":"
          (Term.app
           `IsMaxOn
           [(Term.proj `T "." `reApplyInnerSelf)
            (Term.app
             `sphere
             [(Term.typeAscription "(" (num "0") ":" [`E] ")")
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
            `x₀])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasEigenvector
         [(Term.typeAscription
           "("
           `T
           ":"
           [(Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
           ")")
          (coeNotation
           "↑"
           (Order.CompleteLattice.«term⨆_,_»
            "⨆"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `x)
              [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
            ", "
            (Term.app
             (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
              "rayleigh_quotient")
             [`x])))
          `x₀])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(convert
            "convert"
            []
            (Term.app
             `hT.has_eigenvector_of_is_local_extr_on
             [`hx₀ (Term.app `Or.inr [`hextr.localize])])
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hx₀' []]
              [(Term.typeSpec
                ":"
                («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hx₀'' []]
              [(Term.typeSpec
                ":"
                («term_∈_»
                 `x₀
                 "∈"
                 (Term.app
                  `sphere
                  [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `T.supr_rayleigh_eq_supr_rayleigh_sphere [`hx₀']))]
             "]")
            [])
           []
           (Tactic.refine' "refine'" (Term.app `IsMaxOn.supr_eq [`hx₀'' (Term.hole "_")]))
           []
           (Tactic.intro "intro" [`x `hx])
           []
           (Tactic.dsimp "dsimp" [] [] [] [] [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                 "="
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))]))))))
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `div_le_div_of_le
             [(Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
              (Term.app `hextr [`hx])]))])))
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
         [(convert
           "convert"
           []
           (Term.app
            `hT.has_eigenvector_of_is_local_extr_on
            [`hx₀ (Term.app `Or.inr [`hextr.localize])])
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hx₀' []]
             [(Term.typeSpec
               ":"
               («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hx₀'' []]
             [(Term.typeSpec
               ":"
               («term_∈_»
                `x₀
                "∈"
                (Term.app
                 `sphere
                 [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `T.supr_rayleigh_eq_supr_rayleigh_sphere [`hx₀']))]
            "]")
           [])
          []
          (Tactic.refine' "refine'" (Term.app `IsMaxOn.supr_eq [`hx₀'' (Term.hole "_")]))
          []
          (Tactic.intro "intro" [`x `hx])
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                "="
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))]))))))
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `div_le_div_of_le
            [(Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
             (Term.app `hextr [`hx])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `div_le_div_of_le
        [(Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
         (Term.app `hextr [`hx])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `div_le_div_of_le
       [(Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
        (Term.app `hextr [`hx])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hextr [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hextr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hextr [`hx]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sq_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_le_div_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
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
         [(Term.typeSpec
           ":"
           («term_=_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
            "="
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x `hx])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `IsMaxOn.supr_eq [`hx₀'' (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsMaxOn.supr_eq [`hx₀'' (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `hx₀''
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsMaxOn.supr_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `T.supr_rayleigh_eq_supr_rayleigh_sphere [`hx₀']))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `T.supr_rayleigh_eq_supr_rayleigh_sphere [`hx₀'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T.supr_rayleigh_eq_supr_rayleigh_sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hx₀'' []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            `x₀
            "∈"
            (Term.app
             `sphere
             [(Term.typeAscription "(" (num "0") ":" [`E] ")")
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       `x₀
       "∈"
       (Term.app
        `sphere
        [(Term.typeAscription "(" (num "0") ":" [`E] ")")
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sphere
       [(Term.typeAscription "(" (num "0") ":" [`E] ")")
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (num "0") ":" [`E] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hx₀' []]
         [(Term.typeSpec
           ":"
           («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `hT.has_eigenvector_of_is_local_extr_on
        [`hx₀ (Term.app `Or.inr [`hextr.localize])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hT.has_eigenvector_of_is_local_extr_on [`hx₀ (Term.app `Or.inr [`hextr.localize])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Or.inr [`hextr.localize])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hextr.localize
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Or.inr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Or.inr [`hextr.localize])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hT.has_eigenvector_of_is_local_extr_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasEigenvector
       [(Term.typeAscription
         "("
         `T
         ":"
         [(Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
         ")")
        (coeNotation
         "↑"
         (Order.CompleteLattice.«term⨆_,_»
          "⨆"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
          ", "
          (Term.app
           (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
            "rayleigh_quotient")
           [`x])))
        `x₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (coeNotation
       "↑"
       (Order.CompleteLattice.«term⨆_,_»
        "⨆"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `x)
          [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
        ", "
        (Term.app
         (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
          "rayleigh_quotient")
         [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.CompleteLattice.«term⨆_,_»
       "⨆"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `x)
         [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
       ", "
       (Term.app
        (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
         "rayleigh_quotient")
        [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
        "rayleigh_quotient")
       [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
       "rayleigh_quotient")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1', expected 'IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1._@.Analysis.InnerProductSpace.Rayleigh._hyg.154'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    For a self-adjoint operator `T`, a maximum of the Rayleigh quotient of `T` on a sphere centred
    at the origin is an eigenvector of `T`, with eigenvalue the global supremum of the Rayleigh
    quotient. -/
  theorem
    has_eigenvector_of_is_max_on
    ( hT : IsSelfAdjoint T )
        { x₀ : E }
        ( hx₀ : x₀ ≠ 0 )
        ( hextr : IsMaxOn T . reApplyInnerSelf sphere ( 0 : E ) ‖ x₀ ‖ x₀ )
      : HasEigenvector ( T : E →ₗ[ 𝕜 ] E ) ↑ ⨆ x : { x : E // x ≠ 0 } , rayleigh_quotient x x₀
    :=
      by
        convert hT.has_eigenvector_of_is_local_extr_on hx₀ Or.inr hextr.localize
          have hx₀' : 0 < ‖ x₀ ‖ := by simp [ hx₀ ]
          have hx₀'' : x₀ ∈ sphere ( 0 : E ) ‖ x₀ ‖ := by simp
          rw [ T.supr_rayleigh_eq_supr_rayleigh_sphere hx₀' ]
          refine' IsMaxOn.supr_eq hx₀'' _
          intro x hx
          dsimp
          have : ‖ x ‖ = ‖ x₀ ‖ := by simpa using hx
          rw [ this ]
          exact div_le_div_of_le sq_nonneg ‖ x₀ ‖ hextr hx
#align is_self_adjoint.has_eigenvector_of_is_max_on IsSelfAdjoint.has_eigenvector_of_is_max_on

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For a self-adjoint operator `T`, a minimum of the Rayleigh quotient of `T` on a sphere centred\nat the origin is an eigenvector of `T`, with eigenvalue the global infimum of the Rayleigh\nquotient. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `has_eigenvector_of_is_min_on [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hT] [":" (Term.app `IsSelfAdjoint [`T])] [] ")")
        (Term.implicitBinder "{" [`x₀] [":" `E] "}")
        (Term.explicitBinder "(" [`hx₀] [":" («term_≠_» `x₀ "≠" (num "0"))] [] ")")
        (Term.explicitBinder
         "("
         [`hextr]
         [":"
          (Term.app
           `IsMinOn
           [(Term.proj `T "." `reApplyInnerSelf)
            (Term.app
             `sphere
             [(Term.typeAscription "(" (num "0") ":" [`E] ")")
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
            `x₀])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasEigenvector
         [(Term.typeAscription
           "("
           `T
           ":"
           [(Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
           ")")
          (coeNotation
           "↑"
           (Order.CompleteLattice.«term⨅_,_»
            "⨅"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `x)
              [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
            ", "
            (Term.app
             (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
              "rayleigh_quotient")
             [`x])))
          `x₀])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(convert
            "convert"
            []
            (Term.app
             `hT.has_eigenvector_of_is_local_extr_on
             [`hx₀ (Term.app `Or.inl [`hextr.localize])])
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hx₀' []]
              [(Term.typeSpec
                ":"
                («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hx₀'' []]
              [(Term.typeSpec
                ":"
                («term_∈_»
                 `x₀
                 "∈"
                 (Term.app
                  `sphere
                  [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `T.infi_rayleigh_eq_infi_rayleigh_sphere [`hx₀']))]
             "]")
            [])
           []
           (Tactic.refine' "refine'" (Term.app `IsMinOn.infi_eq [`hx₀'' (Term.hole "_")]))
           []
           (Tactic.intro "intro" [`x `hx])
           []
           (Tactic.dsimp "dsimp" [] [] [] [] [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                 "="
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))]))))))
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `div_le_div_of_le
             [(Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
              (Term.app `hextr [`hx])]))])))
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
         [(convert
           "convert"
           []
           (Term.app
            `hT.has_eigenvector_of_is_local_extr_on
            [`hx₀ (Term.app `Or.inl [`hextr.localize])])
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hx₀' []]
             [(Term.typeSpec
               ":"
               («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hx₀'' []]
             [(Term.typeSpec
               ":"
               («term_∈_»
                `x₀
                "∈"
                (Term.app
                 `sphere
                 [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `T.infi_rayleigh_eq_infi_rayleigh_sphere [`hx₀']))]
            "]")
           [])
          []
          (Tactic.refine' "refine'" (Term.app `IsMinOn.infi_eq [`hx₀'' (Term.hole "_")]))
          []
          (Tactic.intro "intro" [`x `hx])
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                "="
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))]))))))
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `div_le_div_of_le
            [(Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
             (Term.app `hextr [`hx])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `div_le_div_of_le
        [(Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
         (Term.app `hextr [`hx])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `div_le_div_of_le
       [(Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
        (Term.app `hextr [`hx])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hextr [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hextr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hextr [`hx]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sq_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `sq_nonneg [(Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_le_div_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
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
         [(Term.typeSpec
           ":"
           («term_=_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
            "="
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x `hx])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `IsMinOn.infi_eq [`hx₀'' (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsMinOn.infi_eq [`hx₀'' (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `hx₀''
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsMinOn.infi_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `T.infi_rayleigh_eq_infi_rayleigh_sphere [`hx₀']))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `T.infi_rayleigh_eq_infi_rayleigh_sphere [`hx₀'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T.infi_rayleigh_eq_infi_rayleigh_sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hx₀'' []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            `x₀
            "∈"
            (Term.app
             `sphere
             [(Term.typeAscription "(" (num "0") ":" [`E] ")")
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       `x₀
       "∈"
       (Term.app
        `sphere
        [(Term.typeAscription "(" (num "0") ":" [`E] ")")
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sphere
       [(Term.typeAscription "(" (num "0") ":" [`E] ")")
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (num "0") ":" [`E] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hx₀' []]
         [(Term.typeSpec
           ":"
           («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx₀)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `hT.has_eigenvector_of_is_local_extr_on
        [`hx₀ (Term.app `Or.inl [`hextr.localize])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hT.has_eigenvector_of_is_local_extr_on [`hx₀ (Term.app `Or.inl [`hextr.localize])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Or.inl [`hextr.localize])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hextr.localize
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Or.inl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Or.inl [`hextr.localize])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hT.has_eigenvector_of_is_local_extr_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasEigenvector
       [(Term.typeAscription
         "("
         `T
         ":"
         [(Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
         ")")
        (coeNotation
         "↑"
         (Order.CompleteLattice.«term⨅_,_»
          "⨅"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
          ", "
          (Term.app
           (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
            "rayleigh_quotient")
           [`x])))
        `x₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (coeNotation
       "↑"
       (Order.CompleteLattice.«term⨅_,_»
        "⨅"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `x)
          [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
        ", "
        (Term.app
         (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
          "rayleigh_quotient")
         [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.CompleteLattice.«term⨅_,_»
       "⨅"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `x)
         [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
       ", "
       (Term.app
        (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
         "rayleigh_quotient")
        [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
        "rayleigh_quotient")
       [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1
       "rayleigh_quotient")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1', expected 'IsSelfAdjoint.Analysis.InnerProductSpace.Rayleigh.termrayleigh_quotient_1._@.Analysis.InnerProductSpace.Rayleigh._hyg.154'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    For a self-adjoint operator `T`, a minimum of the Rayleigh quotient of `T` on a sphere centred
    at the origin is an eigenvector of `T`, with eigenvalue the global infimum of the Rayleigh
    quotient. -/
  theorem
    has_eigenvector_of_is_min_on
    ( hT : IsSelfAdjoint T )
        { x₀ : E }
        ( hx₀ : x₀ ≠ 0 )
        ( hextr : IsMinOn T . reApplyInnerSelf sphere ( 0 : E ) ‖ x₀ ‖ x₀ )
      : HasEigenvector ( T : E →ₗ[ 𝕜 ] E ) ↑ ⨅ x : { x : E // x ≠ 0 } , rayleigh_quotient x x₀
    :=
      by
        convert hT.has_eigenvector_of_is_local_extr_on hx₀ Or.inl hextr.localize
          have hx₀' : 0 < ‖ x₀ ‖ := by simp [ hx₀ ]
          have hx₀'' : x₀ ∈ sphere ( 0 : E ) ‖ x₀ ‖ := by simp
          rw [ T.infi_rayleigh_eq_infi_rayleigh_sphere hx₀' ]
          refine' IsMinOn.infi_eq hx₀'' _
          intro x hx
          dsimp
          have : ‖ x ‖ = ‖ x₀ ‖ := by simpa using hx
          rw [ this ]
          exact div_le_div_of_le sq_nonneg ‖ x₀ ‖ hextr hx
#align is_self_adjoint.has_eigenvector_of_is_min_on IsSelfAdjoint.has_eigenvector_of_is_min_on

end CompleteSpace

end IsSelfAdjoint

section FiniteDimensional

variable [FiniteDimensional 𝕜 E] [_i : Nontrivial E] {T : E →ₗ[𝕜] E}

namespace LinearMap

namespace IsSymmetric

include _i

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The supremum of the Rayleigh quotient of a symmetric operator `T` on a nontrivial\nfinite-dimensional vector space is an eigenvalue for that operator. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `has_eigenvalue_supr_of_finite_dimensional [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hT] [":" (Term.proj `T "." `IsSymmetric)] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasEigenvalue
         [`T
          (coeNotation
           "↑"
           (Order.CompleteLattice.«term⨆_,_»
            "⨆"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `x)
              [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
            ", "
            («term_/_»
             (Term.app
              `IsROrC.re
              [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫»
                "⟪"
                (Term.app `T [`x])
                ", "
                `x
                "⟫")])
             "/"
             («term_^_»
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Term.typeAscription "(" `x ":" [`E] ")")
               "‖")
              "^"
              (num "2")))))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl [] [] ":=" (Term.app `FiniteDimensional.proper_is_R_or_C [`𝕜 `E]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl (Term.letIdDecl `T' [] [] ":=" `hT.to_self_adjoint)))
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                  [])]
                "⟩")])]
            [":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `E]))
              ","
              («term_≠_» `x "≠" (num "0")))]
            [":=" [(Term.app `exists_ne [(num "0")])]])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`H₁ []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `IsCompact
                 [(Term.app
                   `sphere
                   [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])]))]
              ":="
              (Term.app `is_compact_sphere [(Term.hole "_") (Term.hole "_")]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`H₂ []]
              [(Term.typeSpec
                ":"
                (Term.proj
                 (Term.app
                  `sphere
                  [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
                 "."
                 `Nonempty))]
              ":="
              (Term.anonymousCtor
               "⟨"
               [`x
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
               "⟩"))))
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₀)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx₀')])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hTx₀)])
                  [])]
                "⟩")])]
            []
            [":="
             [(Term.app
               `H₁.exists_forall_ge
               [`H₂ `T'.val.re_apply_inner_self_continuous.continuous_on])]])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hx₀ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
                 "="
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx₀']))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `IsMaxOn
                 [`T'.val.re_apply_inner_self
                  (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
                  `x₀]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    ["only"]
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx₀)]
                      "]")]
                    ["using" `hTx₀]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hx₀_ne []]
              [(Term.typeSpec ":" («term_≠_» `x₀ "≠" (num "0")))]
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
                       («term_≠_»
                        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
                        "≠"
                        (num "0")))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `hx₀)
                            ","
                            (Tactic.simpLemma [] [] `norm_eq_zero)
                            ","
                            (Tactic.simpLemma [] [] `hx)
                            ","
                            (Tactic.simpLemma [] [] `Ne.def)
                            ","
                            (Tactic.simpLemma [] [] `not_false_iff)]
                           "]"]
                          [])]))))))
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
                      [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
                       ","
                       (Tactic.simpLemma [] [] `Ne.def)]
                      "]")]
                    []))]))))))
           []
           (Tactic.exact
            "exact"
            (Term.app
             `has_eigenvalue_of_has_eigenvector
             [(Term.app `T'.prop.has_eigenvector_of_is_max_on [`hx₀_ne `this])]))])))
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
           (Term.haveDecl
            (Term.haveIdDecl [] [] ":=" (Term.app `FiniteDimensional.proper_is_R_or_C [`𝕜 `E]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `T' [] [] ":=" `hT.to_self_adjoint)))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                 [])]
               "⟩")])]
           [":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `E]))
             ","
             («term_≠_» `x "≠" (num "0")))]
           [":=" [(Term.app `exists_ne [(num "0")])]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`H₁ []]
             [(Term.typeSpec
               ":"
               (Term.app
                `IsCompact
                [(Term.app
                  `sphere
                  [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])]))]
             ":="
             (Term.app `is_compact_sphere [(Term.hole "_") (Term.hole "_")]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`H₂ []]
             [(Term.typeSpec
               ":"
               (Term.proj
                (Term.app
                 `sphere
                 [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
                "."
                `Nonempty))]
             ":="
             (Term.anonymousCtor
              "⟨"
              [`x
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
              "⟩"))))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₀)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx₀')])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hTx₀)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              `H₁.exists_forall_ge
              [`H₂ `T'.val.re_apply_inner_self_continuous.continuous_on])]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hx₀ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
                "="
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx₀']))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `IsMaxOn
                [`T'.val.re_apply_inner_self
                 (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
                 `x₀]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   ["only"]
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx₀)]
                     "]")]
                   ["using" `hTx₀]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hx₀_ne []]
             [(Term.typeSpec ":" («term_≠_» `x₀ "≠" (num "0")))]
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
                      («term_≠_»
                       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
                       "≠"
                       (num "0")))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [] `hx₀)
                           ","
                           (Tactic.simpLemma [] [] `norm_eq_zero)
                           ","
                           (Tactic.simpLemma [] [] `hx)
                           ","
                           (Tactic.simpLemma [] [] `Ne.def)
                           ","
                           (Tactic.simpLemma [] [] `not_false_iff)]
                          "]"]
                         [])]))))))
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
                     [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
                      ","
                      (Tactic.simpLemma [] [] `Ne.def)]
                     "]")]
                   []))]))))))
          []
          (Tactic.exact
           "exact"
           (Term.app
            `has_eigenvalue_of_has_eigenvector
            [(Term.app `T'.prop.has_eigenvector_of_is_max_on [`hx₀_ne `this])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `has_eigenvalue_of_has_eigenvector
        [(Term.app `T'.prop.has_eigenvector_of_is_max_on [`hx₀_ne `this])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `has_eigenvalue_of_has_eigenvector
       [(Term.app `T'.prop.has_eigenvector_of_is_max_on [`hx₀_ne `this])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `T'.prop.has_eigenvector_of_is_max_on [`hx₀_ne `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx₀_ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T'.prop.has_eigenvector_of_is_max_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `T'.prop.has_eigenvector_of_is_max_on [`hx₀_ne `this])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `has_eigenvalue_of_has_eigenvector
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hx₀_ne []]
         [(Term.typeSpec ":" («term_≠_» `x₀ "≠" (num "0")))]
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
                  («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `hx₀)
                       ","
                       (Tactic.simpLemma [] [] `norm_eq_zero)
                       ","
                       (Tactic.simpLemma [] [] `hx)
                       ","
                       (Tactic.simpLemma [] [] `Ne.def)
                       ","
                       (Tactic.simpLemma [] [] `not_false_iff)]
                      "]"]
                     [])]))))))
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
                 [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
                  ","
                  (Tactic.simpLemma [] [] `Ne.def)]
                 "]")]
               []))]))))))
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
               («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `hx₀)
                    ","
                    (Tactic.simpLemma [] [] `norm_eq_zero)
                    ","
                    (Tactic.simpLemma [] [] `hx)
                    ","
                    (Tactic.simpLemma [] [] `Ne.def)
                    ","
                    (Tactic.simpLemma [] [] `not_false_iff)]
                   "]"]
                  [])]))))))
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
              [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
               ","
               (Tactic.simpLemma [] [] `Ne.def)]
              "]")]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
          [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
           ","
           (Tactic.simpLemma [] [] `Ne.def)]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ne.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `hx₀)
                ","
                (Tactic.simpLemma [] [] `norm_eq_zero)
                ","
                (Tactic.simpLemma [] [] `hx)
                ","
                (Tactic.simpLemma [] [] `Ne.def)
                ","
                (Tactic.simpLemma [] [] `not_false_iff)]
               "]"]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `hx₀)
             ","
             (Tactic.simpLemma [] [] `norm_eq_zero)
             ","
             (Tactic.simpLemma [] [] `hx)
             ","
             (Tactic.simpLemma [] [] `Ne.def)
             ","
             (Tactic.simpLemma [] [] `not_false_iff)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `hx₀)
         ","
         (Tactic.simpLemma [] [] `norm_eq_zero)
         ","
         (Tactic.simpLemma [] [] `hx)
         ","
         (Tactic.simpLemma [] [] `Ne.def)
         ","
         (Tactic.simpLemma [] [] `not_false_iff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_false_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ne.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `x₀ "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.app
            `IsMaxOn
            [`T'.val.re_apply_inner_self
             (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
             `x₀]))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               ["only"]
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx₀)]
                 "]")]
               ["using" `hTx₀]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx₀)]
              "]")]
            ["using" `hTx₀]))])))
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
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx₀)] "]")]
        ["using" `hTx₀]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hTx₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsMaxOn
       [`T'.val.re_apply_inner_self
        (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
        `x₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `T'.val.re_apply_inner_self
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsMaxOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hx₀ []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
            "="
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx₀']))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx₀']))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx₀']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₀)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx₀')])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hTx₀)])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          `H₁.exists_forall_ge
          [`H₂ `T'.val.re_apply_inner_self_continuous.continuous_on])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H₁.exists_forall_ge [`H₂ `T'.val.re_apply_inner_self_continuous.continuous_on])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `T'.val.re_apply_inner_self_continuous.continuous_on
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H₁.exists_forall_ge
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`H₂ []]
         [(Term.typeSpec
           ":"
           (Term.proj
            (Term.app
             `sphere
             [(Term.typeAscription "(" (num "0") ":" [`E] ")")
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
            "."
            `Nonempty))]
         ":="
         (Term.anonymousCtor
          "⟨"
          [`x
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
          "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`x
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `sphere
        [(Term.typeAscription "(" (num "0") ":" [`E] ")")
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
       "."
       `Nonempty)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `sphere
       [(Term.typeAscription "(" (num "0") ":" [`E] ")")
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (num "0") ":" [`E] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `sphere
      [(Term.typeAscription "(" (num "0") ":" [`E] ")")
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`H₁ []]
         [(Term.typeSpec
           ":"
           (Term.app
            `IsCompact
            [(Term.app
              `sphere
              [(Term.typeAscription "(" (num "0") ":" [`E] ")")
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])]))]
         ":="
         (Term.app `is_compact_sphere [(Term.hole "_") (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_compact_sphere [(Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_compact_sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsCompact
       [(Term.app
         `sphere
         [(Term.typeAscription "(" (num "0") ":" [`E] ")")
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sphere
       [(Term.typeAscription "(" (num "0") ":" [`E] ")")
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (num "0") ":" [`E] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `sphere
      [(Term.typeAscription "(" (num "0") ":" [`E] ")")
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsCompact
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
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
             [])]
           "⟩")])]
       [":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `E]))
         ","
         («term_≠_» `x "≠" (num "0")))]
       [":=" [(Term.app `exists_ne [(num "0")])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `exists_ne [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exists_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `E]))
       ","
       («term_≠_» `x "≠" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `x "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `T' [] [] ":=" `hT.to_self_adjoint)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hT.to_self_adjoint
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticHaveI_
       "haveI"
       (Term.haveDecl
        (Term.haveIdDecl [] [] ":=" (Term.app `FiniteDimensional.proper_is_R_or_C [`𝕜 `E]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `FiniteDimensional.proper_is_R_or_C [`𝕜 `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `FiniteDimensional.proper_is_R_or_C
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasEigenvalue
       [`T
        (coeNotation
         "↑"
         (Order.CompleteLattice.«term⨆_,_»
          "⨆"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
          ", "
          («term_/_»
           (Term.app
            `IsROrC.re
            [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")])
           "/"
           («term_^_»
            (Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             (Term.typeAscription "(" `x ":" [`E] ")")
             "‖")
            "^"
            (num "2")))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation
       "↑"
       (Order.CompleteLattice.«term⨆_,_»
        "⨆"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `x)
          [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
        ", "
        («term_/_»
         (Term.app
          `IsROrC.re
          [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")])
         "/"
         («term_^_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.typeAscription "(" `x ":" [`E] ")") "‖")
          "^"
          (num "2")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.CompleteLattice.«term⨆_,_»
       "⨆"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `x)
         [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
       ", "
       («term_/_»
        (Term.app
         `IsROrC.re
         [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")])
        "/"
        («term_^_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.typeAscription "(" `x ":" [`E] ")") "‖")
         "^"
         (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       (Term.app
        `IsROrC.re
        [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")])
       "/"
       («term_^_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.typeAscription "(" `x ":" [`E] ")") "‖")
        "^"
        (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.typeAscription "(" `x ":" [`E] ")") "‖")
       "^"
       (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.typeAscription "(" `x ":" [`E] ")") "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `x ":" [`E] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app
       `IsROrC.re
       [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Rayleigh.term⟪_,_⟫._@.Analysis.InnerProductSpace.Rayleigh._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The supremum of the Rayleigh quotient of a symmetric operator `T` on a nontrivial
    finite-dimensional vector space is an eigenvalue for that operator. -/
  theorem
    has_eigenvalue_supr_of_finite_dimensional
    ( hT : T . IsSymmetric )
      : HasEigenvalue T ↑ ⨆ x : { x : E // x ≠ 0 } , IsROrC.re ⟪ T x , x ⟫ / ‖ ( x : E ) ‖ ^ 2
    :=
      by
        haveI := FiniteDimensional.proper_is_R_or_C 𝕜 E
          let T' := hT.to_self_adjoint
          obtain ⟨ x , hx ⟩ : ∃ x : E , x ≠ 0 := exists_ne 0
          have H₁ : IsCompact sphere ( 0 : E ) ‖ x ‖ := is_compact_sphere _ _
          have H₂ : sphere ( 0 : E ) ‖ x ‖ . Nonempty := ⟨ x , by simp ⟩
          obtain
            ⟨ x₀ , hx₀' , hTx₀ ⟩
            := H₁.exists_forall_ge H₂ T'.val.re_apply_inner_self_continuous.continuous_on
          have hx₀ : ‖ x₀ ‖ = ‖ x ‖ := by simpa using hx₀'
          have
            : IsMaxOn T'.val.re_apply_inner_self sphere 0 ‖ x₀ ‖ x₀
              :=
              by simpa only [ ← hx₀ ] using hTx₀
          have
            hx₀_ne
              : x₀ ≠ 0
              :=
              by
                have
                    : ‖ x₀ ‖ ≠ 0
                      :=
                      by simp only [ hx₀ , norm_eq_zero , hx , Ne.def , not_false_iff ]
                  simpa [ ← norm_eq_zero , Ne.def ]
          exact has_eigenvalue_of_has_eigenvector T'.prop.has_eigenvector_of_is_max_on hx₀_ne this
#align
  linear_map.is_symmetric.has_eigenvalue_supr_of_finite_dimensional LinearMap.IsSymmetric.has_eigenvalue_supr_of_finite_dimensional

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The infimum of the Rayleigh quotient of a symmetric operator `T` on a nontrivial\nfinite-dimensional vector space is an eigenvalue for that operator. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `has_eigenvalue_infi_of_finite_dimensional [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hT] [":" (Term.proj `T "." `IsSymmetric)] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasEigenvalue
         [`T
          (coeNotation
           "↑"
           (Order.CompleteLattice.«term⨅_,_»
            "⨅"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `x)
              [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
            ", "
            («term_/_»
             (Term.app
              `IsROrC.re
              [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫»
                "⟪"
                (Term.app `T [`x])
                ", "
                `x
                "⟫")])
             "/"
             («term_^_»
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Term.typeAscription "(" `x ":" [`E] ")")
               "‖")
              "^"
              (num "2")))))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl [] [] ":=" (Term.app `FiniteDimensional.proper_is_R_or_C [`𝕜 `E]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl (Term.letIdDecl `T' [] [] ":=" `hT.to_self_adjoint)))
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                  [])]
                "⟩")])]
            [":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `E]))
              ","
              («term_≠_» `x "≠" (num "0")))]
            [":=" [(Term.app `exists_ne [(num "0")])]])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`H₁ []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `IsCompact
                 [(Term.app
                   `sphere
                   [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])]))]
              ":="
              (Term.app `is_compact_sphere [(Term.hole "_") (Term.hole "_")]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`H₂ []]
              [(Term.typeSpec
                ":"
                (Term.proj
                 (Term.app
                  `sphere
                  [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
                 "."
                 `Nonempty))]
              ":="
              (Term.anonymousCtor
               "⟨"
               [`x
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
               "⟩"))))
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₀)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx₀')])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hTx₀)])
                  [])]
                "⟩")])]
            []
            [":="
             [(Term.app
               `H₁.exists_forall_le
               [`H₂ `T'.val.re_apply_inner_self_continuous.continuous_on])]])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hx₀ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
                 "="
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx₀']))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `IsMinOn
                 [`T'.val.re_apply_inner_self
                  (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
                  `x₀]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    ["only"]
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx₀)]
                      "]")]
                    ["using" `hTx₀]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hx₀_ne []]
              [(Term.typeSpec ":" («term_≠_» `x₀ "≠" (num "0")))]
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
                       («term_≠_»
                        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
                        "≠"
                        (num "0")))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `hx₀)
                            ","
                            (Tactic.simpLemma [] [] `norm_eq_zero)
                            ","
                            (Tactic.simpLemma [] [] `hx)
                            ","
                            (Tactic.simpLemma [] [] `Ne.def)
                            ","
                            (Tactic.simpLemma [] [] `not_false_iff)]
                           "]"]
                          [])]))))))
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
                      [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
                       ","
                       (Tactic.simpLemma [] [] `Ne.def)]
                      "]")]
                    []))]))))))
           []
           (Tactic.exact
            "exact"
            (Term.app
             `has_eigenvalue_of_has_eigenvector
             [(Term.app `T'.prop.has_eigenvector_of_is_min_on [`hx₀_ne `this])]))])))
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
           (Term.haveDecl
            (Term.haveIdDecl [] [] ":=" (Term.app `FiniteDimensional.proper_is_R_or_C [`𝕜 `E]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `T' [] [] ":=" `hT.to_self_adjoint)))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                 [])]
               "⟩")])]
           [":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `E]))
             ","
             («term_≠_» `x "≠" (num "0")))]
           [":=" [(Term.app `exists_ne [(num "0")])]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`H₁ []]
             [(Term.typeSpec
               ":"
               (Term.app
                `IsCompact
                [(Term.app
                  `sphere
                  [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])]))]
             ":="
             (Term.app `is_compact_sphere [(Term.hole "_") (Term.hole "_")]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`H₂ []]
             [(Term.typeSpec
               ":"
               (Term.proj
                (Term.app
                 `sphere
                 [(Term.typeAscription "(" (num "0") ":" [`E] ")")
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
                "."
                `Nonempty))]
             ":="
             (Term.anonymousCtor
              "⟨"
              [`x
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
              "⟩"))))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₀)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx₀')])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hTx₀)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              `H₁.exists_forall_le
              [`H₂ `T'.val.re_apply_inner_self_continuous.continuous_on])]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hx₀ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
                "="
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx₀']))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `IsMinOn
                [`T'.val.re_apply_inner_self
                 (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
                 `x₀]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   ["only"]
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx₀)]
                     "]")]
                   ["using" `hTx₀]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hx₀_ne []]
             [(Term.typeSpec ":" («term_≠_» `x₀ "≠" (num "0")))]
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
                      («term_≠_»
                       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
                       "≠"
                       (num "0")))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [] `hx₀)
                           ","
                           (Tactic.simpLemma [] [] `norm_eq_zero)
                           ","
                           (Tactic.simpLemma [] [] `hx)
                           ","
                           (Tactic.simpLemma [] [] `Ne.def)
                           ","
                           (Tactic.simpLemma [] [] `not_false_iff)]
                          "]"]
                         [])]))))))
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
                     [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
                      ","
                      (Tactic.simpLemma [] [] `Ne.def)]
                     "]")]
                   []))]))))))
          []
          (Tactic.exact
           "exact"
           (Term.app
            `has_eigenvalue_of_has_eigenvector
            [(Term.app `T'.prop.has_eigenvector_of_is_min_on [`hx₀_ne `this])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `has_eigenvalue_of_has_eigenvector
        [(Term.app `T'.prop.has_eigenvector_of_is_min_on [`hx₀_ne `this])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `has_eigenvalue_of_has_eigenvector
       [(Term.app `T'.prop.has_eigenvector_of_is_min_on [`hx₀_ne `this])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `T'.prop.has_eigenvector_of_is_min_on [`hx₀_ne `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx₀_ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T'.prop.has_eigenvector_of_is_min_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `T'.prop.has_eigenvector_of_is_min_on [`hx₀_ne `this])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `has_eigenvalue_of_has_eigenvector
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hx₀_ne []]
         [(Term.typeSpec ":" («term_≠_» `x₀ "≠" (num "0")))]
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
                  («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `hx₀)
                       ","
                       (Tactic.simpLemma [] [] `norm_eq_zero)
                       ","
                       (Tactic.simpLemma [] [] `hx)
                       ","
                       (Tactic.simpLemma [] [] `Ne.def)
                       ","
                       (Tactic.simpLemma [] [] `not_false_iff)]
                      "]"]
                     [])]))))))
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
                 [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
                  ","
                  (Tactic.simpLemma [] [] `Ne.def)]
                 "]")]
               []))]))))))
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
               («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `hx₀)
                    ","
                    (Tactic.simpLemma [] [] `norm_eq_zero)
                    ","
                    (Tactic.simpLemma [] [] `hx)
                    ","
                    (Tactic.simpLemma [] [] `Ne.def)
                    ","
                    (Tactic.simpLemma [] [] `not_false_iff)]
                   "]"]
                  [])]))))))
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
              [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
               ","
               (Tactic.simpLemma [] [] `Ne.def)]
              "]")]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
          [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `norm_eq_zero)
           ","
           (Tactic.simpLemma [] [] `Ne.def)]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ne.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `hx₀)
                ","
                (Tactic.simpLemma [] [] `norm_eq_zero)
                ","
                (Tactic.simpLemma [] [] `hx)
                ","
                (Tactic.simpLemma [] [] `Ne.def)
                ","
                (Tactic.simpLemma [] [] `not_false_iff)]
               "]"]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `hx₀)
             ","
             (Tactic.simpLemma [] [] `norm_eq_zero)
             ","
             (Tactic.simpLemma [] [] `hx)
             ","
             (Tactic.simpLemma [] [] `Ne.def)
             ","
             (Tactic.simpLemma [] [] `not_false_iff)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `hx₀)
         ","
         (Tactic.simpLemma [] [] `norm_eq_zero)
         ","
         (Tactic.simpLemma [] [] `hx)
         ","
         (Tactic.simpLemma [] [] `Ne.def)
         ","
         (Tactic.simpLemma [] [] `not_false_iff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_false_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ne.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖") "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `x₀ "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.app
            `IsMinOn
            [`T'.val.re_apply_inner_self
             (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
             `x₀]))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               ["only"]
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx₀)]
                 "]")]
               ["using" `hTx₀]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx₀)]
              "]")]
            ["using" `hTx₀]))])))
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
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx₀)] "]")]
        ["using" `hTx₀]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hTx₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsMinOn
       [`T'.val.re_apply_inner_self
        (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
        `x₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `sphere [(num "0") (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `T'.val.re_apply_inner_self
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsMinOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hx₀ []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
            "="
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx₀']))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx₀']))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hx₀']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx₀'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x₀ "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₀)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx₀')])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hTx₀)])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          `H₁.exists_forall_le
          [`H₂ `T'.val.re_apply_inner_self_continuous.continuous_on])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H₁.exists_forall_le [`H₂ `T'.val.re_apply_inner_self_continuous.continuous_on])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `T'.val.re_apply_inner_self_continuous.continuous_on
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H₁.exists_forall_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`H₂ []]
         [(Term.typeSpec
           ":"
           (Term.proj
            (Term.app
             `sphere
             [(Term.typeAscription "(" (num "0") ":" [`E] ")")
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
            "."
            `Nonempty))]
         ":="
         (Term.anonymousCtor
          "⟨"
          [`x
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
          "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`x
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `sphere
        [(Term.typeAscription "(" (num "0") ":" [`E] ")")
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
       "."
       `Nonempty)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `sphere
       [(Term.typeAscription "(" (num "0") ":" [`E] ")")
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (num "0") ":" [`E] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `sphere
      [(Term.typeAscription "(" (num "0") ":" [`E] ")")
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`H₁ []]
         [(Term.typeSpec
           ":"
           (Term.app
            `IsCompact
            [(Term.app
              `sphere
              [(Term.typeAscription "(" (num "0") ":" [`E] ")")
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])]))]
         ":="
         (Term.app `is_compact_sphere [(Term.hole "_") (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_compact_sphere [(Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_compact_sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsCompact
       [(Term.app
         `sphere
         [(Term.typeAscription "(" (num "0") ":" [`E] ")")
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sphere
       [(Term.typeAscription "(" (num "0") ":" [`E] ")")
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (num "0") ":" [`E] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sphere
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `sphere
      [(Term.typeAscription "(" (num "0") ":" [`E] ")")
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsCompact
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
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
             [])]
           "⟩")])]
       [":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `E]))
         ","
         («term_≠_» `x "≠" (num "0")))]
       [":=" [(Term.app `exists_ne [(num "0")])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `exists_ne [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exists_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `E]))
       ","
       («term_≠_» `x "≠" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `x "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `T' [] [] ":=" `hT.to_self_adjoint)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hT.to_self_adjoint
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticHaveI_
       "haveI"
       (Term.haveDecl
        (Term.haveIdDecl [] [] ":=" (Term.app `FiniteDimensional.proper_is_R_or_C [`𝕜 `E]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `FiniteDimensional.proper_is_R_or_C [`𝕜 `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `FiniteDimensional.proper_is_R_or_C
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasEigenvalue
       [`T
        (coeNotation
         "↑"
         (Order.CompleteLattice.«term⨅_,_»
          "⨅"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `x)
            [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
          ", "
          («term_/_»
           (Term.app
            `IsROrC.re
            [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")])
           "/"
           («term_^_»
            (Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             (Term.typeAscription "(" `x ":" [`E] ")")
             "‖")
            "^"
            (num "2")))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation
       "↑"
       (Order.CompleteLattice.«term⨅_,_»
        "⨅"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `x)
          [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
        ", "
        («term_/_»
         (Term.app
          `IsROrC.re
          [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")])
         "/"
         («term_^_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.typeAscription "(" `x ":" [`E] ")") "‖")
          "^"
          (num "2")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.CompleteLattice.«term⨅_,_»
       "⨅"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `x)
         [(group ":" («term{_:_//_}» "{" `x [":" `E] "//" («term_≠_» `x "≠" (num "0")) "}"))]))
       ", "
       («term_/_»
        (Term.app
         `IsROrC.re
         [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")])
        "/"
        («term_^_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.typeAscription "(" `x ":" [`E] ")") "‖")
         "^"
         (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       (Term.app
        `IsROrC.re
        [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")])
       "/"
       («term_^_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.typeAscription "(" `x ":" [`E] ")") "‖")
        "^"
        (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.typeAscription "(" `x ":" [`E] ")") "‖")
       "^"
       (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.typeAscription "(" `x ":" [`E] ")") "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `x ":" [`E] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app
       `IsROrC.re
       [(Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Rayleigh.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Rayleigh.term⟪_,_⟫._@.Analysis.InnerProductSpace.Rayleigh._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The infimum of the Rayleigh quotient of a symmetric operator `T` on a nontrivial
    finite-dimensional vector space is an eigenvalue for that operator. -/
  theorem
    has_eigenvalue_infi_of_finite_dimensional
    ( hT : T . IsSymmetric )
      : HasEigenvalue T ↑ ⨅ x : { x : E // x ≠ 0 } , IsROrC.re ⟪ T x , x ⟫ / ‖ ( x : E ) ‖ ^ 2
    :=
      by
        haveI := FiniteDimensional.proper_is_R_or_C 𝕜 E
          let T' := hT.to_self_adjoint
          obtain ⟨ x , hx ⟩ : ∃ x : E , x ≠ 0 := exists_ne 0
          have H₁ : IsCompact sphere ( 0 : E ) ‖ x ‖ := is_compact_sphere _ _
          have H₂ : sphere ( 0 : E ) ‖ x ‖ . Nonempty := ⟨ x , by simp ⟩
          obtain
            ⟨ x₀ , hx₀' , hTx₀ ⟩
            := H₁.exists_forall_le H₂ T'.val.re_apply_inner_self_continuous.continuous_on
          have hx₀ : ‖ x₀ ‖ = ‖ x ‖ := by simpa using hx₀'
          have
            : IsMinOn T'.val.re_apply_inner_self sphere 0 ‖ x₀ ‖ x₀
              :=
              by simpa only [ ← hx₀ ] using hTx₀
          have
            hx₀_ne
              : x₀ ≠ 0
              :=
              by
                have
                    : ‖ x₀ ‖ ≠ 0
                      :=
                      by simp only [ hx₀ , norm_eq_zero , hx , Ne.def , not_false_iff ]
                  simpa [ ← norm_eq_zero , Ne.def ]
          exact has_eigenvalue_of_has_eigenvector T'.prop.has_eigenvector_of_is_min_on hx₀_ne this
#align
  linear_map.is_symmetric.has_eigenvalue_infi_of_finite_dimensional LinearMap.IsSymmetric.has_eigenvalue_infi_of_finite_dimensional

omit _i

theorem subsingleton_of_no_eigenvalue_finite_dimensional (hT : T.IsSymmetric)
    (hT' : ∀ μ : 𝕜, Module.EndCat.eigenspace (T : E →ₗ[𝕜] E) μ = ⊥) : Subsingleton E :=
  (subsingleton_or_nontrivial E).resolve_right fun h =>
    absurd (hT' _) hT.has_eigenvalue_supr_of_finite_dimensional
#align
  linear_map.is_symmetric.subsingleton_of_no_eigenvalue_finite_dimensional LinearMap.IsSymmetric.subsingleton_of_no_eigenvalue_finite_dimensional

end IsSymmetric

end LinearMap

end FiniteDimensional

