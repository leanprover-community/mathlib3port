/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.integral.vitali_caratheodory
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.Regular
import Mathbin.Topology.Semicontinuous
import Mathbin.MeasureTheory.Integral.Bochner
import Mathbin.Topology.Instances.Ereal

/-!
# Vitali-Carathéodory theorem

Vitali-Carathéodory theorem asserts the following. Consider an integrable function `f : α → ℝ` on
a space with a regular measure. Then there exists a function `g : α → ereal` such that `f x < g x`
everywhere, `g` is lower semicontinuous, and the integral of `g` is arbitrarily close to that of
`f`. This theorem is proved in this file, as `exists_lt_lower_semicontinuous_integral_lt`.

Symmetrically, there exists `g < f` which is upper semicontinuous, with integral arbitrarily close
to that of `f`. It follows from the previous statement applied to `-f`. It is formalized under
the name `exists_upper_semicontinuous_lt_integral_gt`.

The most classical version of Vitali-Carathéodory theorem only ensures a large inequality
`f x ≤ g x`. For applications to the fundamental theorem of calculus, though, the strict inequality
`f x < g x` is important. Therefore, we prove the stronger version with strict inequalities in this
file. There is a price to pay: we require that the measure is `σ`-finite, which is not necessary for
the classical Vitali-Carathéodory theorem. Since this is satisfied in all applications, this is
not a real problem.

## Sketch of proof

Decomposing `f` as the difference of its positive and negative parts, it suffices to show that a
positive function can be bounded from above by a lower semicontinuous function, and from below
by an upper semicontinuous function, with integrals close to that of `f`.

For the bound from above, write `f` as a series `∑' n, cₙ * indicator (sₙ)` of simple functions.
Then, approximate `sₙ` by a larger open set `uₙ` with measure very close to that of `sₙ` (this is
possible by regularity of the measure), and set `g = ∑' n, cₙ * indicator (uₙ)`. It is
lower semicontinuous as a series of lower semicontinuous functions, and its integral is arbitrarily
close to that of `f`.

For the bound from below, use finitely many terms in the series, and approximate `sₙ` from inside by
a closed set `Fₙ`. Then `∑ n < N, cₙ * indicator (Fₙ)` is bounded from above by `f`, it is
upper semicontinuous as a finite sum of upper semicontinuous functions, and its integral is
arbitrarily close to that of `f`.

The main pain point in the implementation is that one needs to jump between the spaces `ℝ`, `ℝ≥0`,
`ℝ≥0∞` and `ereal` (and be careful that addition is not well behaved on `ereal`), and between
`lintegral` and `integral`.

We first show the bound from above for simple functions and the nonnegative integral
(this is the main nontrivial mathematical point), then deduce it for general nonnegative functions,
first for the nonnegative integral and then for the Bochner integral.

Then we follow the same steps for the lower bound.

Finally, we glue them together to obtain the main statement
`exists_lt_lower_semicontinuous_integral_lt`.

## Related results

Are you looking for a result on approximation by continuous functions (not just semicontinuous)?
See result `measure_theory.Lp.continuous_map_dense`, in the file
`measure_theory.continuous_map_dense`.

## References

[Rudin, *Real and Complex Analysis* (Theorem 2.24)][rudin2006real]

-/


open Ennreal Nnreal

open MeasureTheory MeasureTheory.Measure

variable {α : Type _} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] (μ : Measure α)
  [WeaklyRegular μ]

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

/-! ### Lower semicontinuous upper bound for nonnegative functions -/


/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (u «expr ⊇ » s) -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given a simple function `f` with values in `ℝ≥0`, there exists a lower semicontinuous\nfunction `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of\n`lintegral`.\nAuxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `SimpleFunc.exists_le_lower_semicontinuous_lintegral_ge [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»
           `α
           " →ₛ "
           (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]
         []
         ")")
        (Term.implicitBinder "{" [`ε] [":" (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] "}")
        (Term.explicitBinder "(" [`ε0] [":" («term_≠_» `ε "≠" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `g)]
           [":" (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
         ","
         («term_∧_»
          (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `f [`x]) "≤" (Term.app `g [`x])))
          "∧"
          («term_∧_»
           (Term.app `LowerSemicontinuous [`g])
           "∧"
           («term_≤_»
            (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
             "∫⁻"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             ", "
             (Term.app `g [`x])
             " ∂"
             `μ)
            "≤"
            («term_+_»
             (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
              "∫⁻"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
              ", "
              (Term.app `f [`x])
              " ∂"
              `μ)
             "+"
             `ε)))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `f)]
            ["using" `MeasureTheory.SimpleFunc.induction]
            ["with"
             [(Lean.binderIdent `c)
              (Lean.binderIdent `s)
              (Lean.binderIdent `hs)
              (Lean.binderIdent `f₁)
              (Lean.binderIdent `f₂)
              (Lean.binderIdent `H)
              (Lean.binderIdent `h₁)
              (Lean.binderIdent `h₂)]]
            ["generalizing" [`ε]])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `f
                []
                []
                ":="
                (Term.app
                 `simple_func.piecewise
                 [`s
                  `hs
                  (Term.app `simple_func.const [`α `c])
                  (Term.app `simple_func.const [`α (num "0")])]))))
             []
             (Classical.«tacticBy_cases_:_»
              "by_cases"
              [`h ":"]
              («term_=_»
               (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                "∫⁻"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                ", "
                (Term.app `f [`x])
                " ∂"
                `μ)
               "="
               (Order.BoundedOrder.«term⊤» "⊤")))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))
                  ","
                  (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
                  ","
                  `lower_semicontinuous_const
                  ","
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
                        [(Tactic.simpLemma [] [] `Ennreal.top_add)
                         ","
                         (Tactic.simpLemma [] [] `le_top)
                         ","
                         (Tactic.simpLemma [] [] `h)]
                        "]"]
                       [])])))]
                 "⟩"))
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `simple_func.coe_const)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.const_zero)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_zero)
                  ","
                  (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
                 "]"]
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `Set.indicator_le_self
                 [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
             []
             (Classical.«tacticBy_cases_:_» "by_cases" [`hc ":"] («term_=_» `c "=" (num "0")))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
                  ","
                  (Term.hole "_")
                  ","
                  `lower_semicontinuous_const
                  ","
                  (Term.hole "_")]
                 "⟩"))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `hc)
                    ","
                    (Tactic.simpLemma [] [] `Set.indicator_zero')
                    ","
                    (Tactic.simpLemma [] [] `Pi.zero_apply)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.const_zero)
                    ","
                    (Tactic.simpLemma [] [] `imp_true_iff)
                    ","
                    (Tactic.simpLemma [] [] `eq_self_iff_true)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_zero)
                    ","
                    (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                    ","
                    (Tactic.simpLemma [] [] `le_zero_iff)]
                   "]"]
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
                   [(Tactic.simpLemma [] [] `lintegral_const)
                    ","
                    (Tactic.simpLemma [] [] `zero_mul)
                    ","
                    (Tactic.simpLemma [] [] `zero_le)
                    ","
                    (Tactic.simpLemma [] [] `Ennreal.coe_zero)]
                   "]"]
                  [])])])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_<_»
                   (Term.app `μ [`s])
                   "<"
                   («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))))]
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
                         («term_<_»
                          (Term.typeAscription
                           "("
                           (num "0")
                           ":"
                           [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                           ")")
                          "<"
                          («term_/_» `ε "/" `c)))]
                       ":="
                       (Term.app
                        (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
                        [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")]))))
                    []
                    (Std.Tactic.Simpa.simpa
                     "simpa"
                     []
                     []
                     (Std.Tactic.Simpa.simpaArgsRest
                      []
                      []
                      []
                      []
                      ["using" (Term.app `Ennreal.add_lt_add_left [(Term.hole "_") `this])]))
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
                        [(Tactic.simpLemma [] [] `hs)
                         ","
                         (Tactic.simpLemma [] [] `hc)
                         ","
                         (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
                         ","
                         (Tactic.simpLemma [] [] `true_and_iff)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_const)
                         ","
                         (Tactic.simpLemma [] [] `Function.const_apply)
                         ","
                         (Tactic.simpLemma [] [] `lintegral_const)
                         ","
                         (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                         ","
                         (Tactic.simpLemma [] [] `Set.univ_inter)
                         ","
                         (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
                         ","
                         (Tactic.simpLemma [] [] `MeasurableSet.univ)
                         ","
                         (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.const_zero)
                         ","
                         (Tactic.simpLemma [] [] `or_false_iff)
                         ","
                         (Tactic.simpLemma [] [] `lintegral_indicator)
                         ","
                         (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
                         ","
                         (Tactic.simpLemma [] [] `Ne.def)
                         ","
                         (Tactic.simpLemma [] [] `not_false_iff)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_zero)
                         ","
                         (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                         ","
                         (Tactic.simpLemma [] [] `false_and_iff)
                         ","
                         (Tactic.simpLemma [] [] `restrict_apply)]
                        "]")]
                      ["using" `h]))]))))))
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `su)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u_open)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `μu)])
                    [])]
                  "⟩")])]
              [":"
               («term∃_,_»
                "∃"
                (Lean.explicitBinders
                 [(Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent `u)]
                   ":"
                   (Term.hole "_")
                   ")")
                  (Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent (Term.hole "_"))]
                   ":"
                   (Init.Core.«term_⊇_» `u " ⊇ " `s)
                   ")")])
                ","
                («term_∧_»
                 (Term.app `IsOpen [`u])
                 "∧"
                 («term_<_»
                  (Term.app `μ [`u])
                  "<"
                  («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c)))))]
              [":=" [(Term.app `s.exists_is_open_lt_of_lt [(Term.hole "_") `this])]])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.app `Set.indicator [`u (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
                ","
                (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
                ","
                (Term.app
                 `u_open.lower_semicontinuous_indicator
                 [(Term.app `zero_le [(Term.hole "_")])])
                ","
                (Term.hole "_")]
               "⟩"))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `simple_func.coe_const)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.const_zero)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_zero)
                  ","
                  (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
                 "]"]
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `Set.indicator_le_indicator_of_subset
                 [`su
                  (Term.fun
                   "fun"
                   (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
                  (Term.hole "_")]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.tacticSuffices_
                "suffices"
                (Term.sufficesDecl
                 []
                 («term_≤_»
                  («term_*_»
                   (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
                   "*"
                   (Term.app `μ [`u]))
                  "≤"
                  («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
                 (Term.byTactic'
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
                         [(Tactic.simpLemma [] [] `hs)
                          ","
                          (Tactic.simpLemma [] [] `u_open.measurable_set)
                          ","
                          (Tactic.simpLemma [] [] `simple_func.coe_const)
                          ","
                          (Tactic.simpLemma [] [] `Function.const_apply)
                          ","
                          (Tactic.simpLemma [] [] `lintegral_const)
                          ","
                          (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                          ","
                          (Tactic.simpLemma [] [] `Set.univ_inter)
                          ","
                          (Tactic.simpLemma [] [] `MeasurableSet.univ)
                          ","
                          (Tactic.simpLemma [] [] `simple_func.const_zero)
                          ","
                          (Tactic.simpLemma [] [] `lintegral_indicator)
                          ","
                          (Tactic.simpLemma [] [] `simple_func.coe_zero)
                          ","
                          (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                          ","
                          (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                          ","
                          (Tactic.simpLemma [] [] `restrict_apply)]
                         "]")]
                       []))])))))
               []
               (calcTactic
                "calc"
                (calcStep
                 («term_≤_»
                  («term_*_»
                   (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
                   "*"
                   (Term.app `μ [`u]))
                  "≤"
                  («term_*_» `c "*" («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))))
                 ":="
                 (Term.app `Ennreal.mul_le_mul [`le_rfl `μu.le]))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Mathlib.Tactic.tacticSimp_rw__
                       "simp_rw"
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
                       [])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule
                          []
                          (Term.app
                           `Ennreal.mul_div_cancel'
                           [(Term.hole "_") `Ennreal.coe_ne_top]))]
                        "]")
                       [])
                      []
                      (Std.Tactic.Simpa.simpa
                       "simpa"
                       []
                       []
                       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))]))))])])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app `h₁ [(Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₁_le_g₁)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁cont)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁int)])
                     [])]
                   "⟩")])
                [])])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app `h₂ [(Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₂_le_g₂)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂cont)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂int)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`x]
                  []
                  "=>"
                  («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`x]
                  []
                  "=>"
                  (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
                ","
                (Term.app `g₁cont.add [`g₂cont])
                ","
                (Term.hole "_")]
               "⟩"))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `simple_func.coe_add)
                ","
                (Tactic.simpLemma [] [] `Ennreal.coe_add)
                ","
                (Tactic.simpLemma [] [] `Pi.add_apply)]
               "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))
                ","
                (Tactic.rwRule
                 []
                 (Term.app `lintegral_add_left [`g₁cont.measurable.coe_nnreal_ennreal]))]
               "]")
              [])
             []
             (convert "convert" [] (Term.app `add_le_add [`g₁int `g₂int]) ["using" (num "1")])
             []
             (Tactic.simp "simp" [] [] ["only"] [] [])
             []
             (Mathlib.Tactic.Conv.convLHS
              "conv_lhs"
              []
              []
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(Tactic.Conv.convRw__
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `Ennreal.add_halves [`ε]))]
                   "]"))])))
             []
             (Tactic.abel "abel" [] [])])])))
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
         [(Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `f)]
           ["using" `MeasureTheory.SimpleFunc.induction]
           ["with"
            [(Lean.binderIdent `c)
             (Lean.binderIdent `s)
             (Lean.binderIdent `hs)
             (Lean.binderIdent `f₁)
             (Lean.binderIdent `f₂)
             (Lean.binderIdent `H)
             (Lean.binderIdent `h₁)
             (Lean.binderIdent `h₂)]]
           ["generalizing" [`ε]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `f
               []
               []
               ":="
               (Term.app
                `simple_func.piecewise
                [`s
                 `hs
                 (Term.app `simple_func.const [`α `c])
                 (Term.app `simple_func.const [`α (num "0")])]))))
            []
            (Classical.«tacticBy_cases_:_»
             "by_cases"
             [`h ":"]
             («term_=_»
              (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
               "∫⁻"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
               ", "
               (Term.app `f [`x])
               " ∂"
               `μ)
              "="
              (Order.BoundedOrder.«term⊤» "⊤")))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))
                 ","
                 (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
                 ","
                 `lower_semicontinuous_const
                 ","
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
                       [(Tactic.simpLemma [] [] `Ennreal.top_add)
                        ","
                        (Tactic.simpLemma [] [] `le_top)
                        ","
                        (Tactic.simpLemma [] [] `h)]
                       "]"]
                      [])])))]
                "⟩"))
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `simple_func.coe_const)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.const_zero)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_zero)
                 ","
                 (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
                "]"]
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `Set.indicator_le_self
                [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
            []
            (Classical.«tacticBy_cases_:_» "by_cases" [`hc ":"] («term_=_» `c "=" (num "0")))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
                 ","
                 (Term.hole "_")
                 ","
                 `lower_semicontinuous_const
                 ","
                 (Term.hole "_")]
                "⟩"))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `hc)
                   ","
                   (Tactic.simpLemma [] [] `Set.indicator_zero')
                   ","
                   (Tactic.simpLemma [] [] `Pi.zero_apply)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.const_zero)
                   ","
                   (Tactic.simpLemma [] [] `imp_true_iff)
                   ","
                   (Tactic.simpLemma [] [] `eq_self_iff_true)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_zero)
                   ","
                   (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                   ","
                   (Tactic.simpLemma [] [] `le_zero_iff)]
                  "]"]
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
                  [(Tactic.simpLemma [] [] `lintegral_const)
                   ","
                   (Tactic.simpLemma [] [] `zero_mul)
                   ","
                   (Tactic.simpLemma [] [] `zero_le)
                   ","
                   (Tactic.simpLemma [] [] `Ennreal.coe_zero)]
                  "]"]
                 [])])])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_<_»
                  (Term.app `μ [`s])
                  "<"
                  («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))))]
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
                        («term_<_»
                         (Term.typeAscription
                          "("
                          (num "0")
                          ":"
                          [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                          ")")
                         "<"
                         («term_/_» `ε "/" `c)))]
                      ":="
                      (Term.app
                       (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
                       [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")]))))
                   []
                   (Std.Tactic.Simpa.simpa
                    "simpa"
                    []
                    []
                    (Std.Tactic.Simpa.simpaArgsRest
                     []
                     []
                     []
                     []
                     ["using" (Term.app `Ennreal.add_lt_add_left [(Term.hole "_") `this])]))
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
                       [(Tactic.simpLemma [] [] `hs)
                        ","
                        (Tactic.simpLemma [] [] `hc)
                        ","
                        (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
                        ","
                        (Tactic.simpLemma [] [] `true_and_iff)
                        ","
                        (Tactic.simpLemma [] [] `simple_func.coe_const)
                        ","
                        (Tactic.simpLemma [] [] `Function.const_apply)
                        ","
                        (Tactic.simpLemma [] [] `lintegral_const)
                        ","
                        (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                        ","
                        (Tactic.simpLemma [] [] `Set.univ_inter)
                        ","
                        (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
                        ","
                        (Tactic.simpLemma [] [] `MeasurableSet.univ)
                        ","
                        (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
                        ","
                        (Tactic.simpLemma [] [] `simple_func.const_zero)
                        ","
                        (Tactic.simpLemma [] [] `or_false_iff)
                        ","
                        (Tactic.simpLemma [] [] `lintegral_indicator)
                        ","
                        (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
                        ","
                        (Tactic.simpLemma [] [] `Ne.def)
                        ","
                        (Tactic.simpLemma [] [] `not_false_iff)
                        ","
                        (Tactic.simpLemma [] [] `simple_func.coe_zero)
                        ","
                        (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                        ","
                        (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                        ","
                        (Tactic.simpLemma [] [] `false_and_iff)
                        ","
                        (Tactic.simpLemma [] [] `restrict_apply)]
                       "]")]
                     ["using" `h]))]))))))
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `su)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u_open)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `μu)])
                   [])]
                 "⟩")])]
             [":"
              («term∃_,_»
               "∃"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `u)] ":" (Term.hole "_") ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent (Term.hole "_"))]
                  ":"
                  (Init.Core.«term_⊇_» `u " ⊇ " `s)
                  ")")])
               ","
               («term_∧_»
                (Term.app `IsOpen [`u])
                "∧"
                («term_<_»
                 (Term.app `μ [`u])
                 "<"
                 («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c)))))]
             [":=" [(Term.app `s.exists_is_open_lt_of_lt [(Term.hole "_") `this])]])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `Set.indicator [`u (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
               ","
               (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
               ","
               (Term.app
                `u_open.lower_semicontinuous_indicator
                [(Term.app `zero_le [(Term.hole "_")])])
               ","
               (Term.hole "_")]
              "⟩"))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `simple_func.coe_const)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.const_zero)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_zero)
                 ","
                 (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
                "]"]
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `Set.indicator_le_indicator_of_subset
                [`su
                 (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
                 (Term.hole "_")]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.tacticSuffices_
               "suffices"
               (Term.sufficesDecl
                []
                («term_≤_»
                 («term_*_»
                  (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
                  "*"
                  (Term.app `μ [`u]))
                 "≤"
                 («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
                (Term.byTactic'
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
                        [(Tactic.simpLemma [] [] `hs)
                         ","
                         (Tactic.simpLemma [] [] `u_open.measurable_set)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_const)
                         ","
                         (Tactic.simpLemma [] [] `Function.const_apply)
                         ","
                         (Tactic.simpLemma [] [] `lintegral_const)
                         ","
                         (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                         ","
                         (Tactic.simpLemma [] [] `Set.univ_inter)
                         ","
                         (Tactic.simpLemma [] [] `MeasurableSet.univ)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.const_zero)
                         ","
                         (Tactic.simpLemma [] [] `lintegral_indicator)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_zero)
                         ","
                         (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                         ","
                         (Tactic.simpLemma [] [] `restrict_apply)]
                        "]")]
                      []))])))))
              []
              (calcTactic
               "calc"
               (calcStep
                («term_≤_»
                 («term_*_»
                  (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
                  "*"
                  (Term.app `μ [`u]))
                 "≤"
                 («term_*_» `c "*" («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))))
                ":="
                (Term.app `Ennreal.mul_le_mul [`le_rfl `μu.le]))
               [(calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Mathlib.Tactic.tacticSimp_rw__
                      "simp_rw"
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
                      [])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         []
                         (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
                       "]")
                      [])
                     []
                     (Std.Tactic.Simpa.simpa
                      "simpa"
                      []
                      []
                      (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))]))))])])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app `h₁ [(Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₁_le_g₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁cont)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁int)])
                    [])]
                  "⟩")])
               [])])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app `h₂ [(Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₂_le_g₂)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂cont)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂int)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
               ","
               (Term.app `g₁cont.add [`g₂cont])
               ","
               (Term.hole "_")]
              "⟩"))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `simple_func.coe_add)
               ","
               (Tactic.simpLemma [] [] `Ennreal.coe_add)
               ","
               (Tactic.simpLemma [] [] `Pi.add_apply)]
              "]"]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))
               ","
               (Tactic.rwRule
                []
                (Term.app `lintegral_add_left [`g₁cont.measurable.coe_nnreal_ennreal]))]
              "]")
             [])
            []
            (convert "convert" [] (Term.app `add_le_add [`g₁int `g₂int]) ["using" (num "1")])
            []
            (Tactic.simp "simp" [] [] ["only"] [] [])
            []
            (Mathlib.Tactic.Conv.convLHS
             "conv_lhs"
             []
             []
             "=>"
             (Tactic.Conv.convSeq
              (Tactic.Conv.convSeq1Indented
               [(Tactic.Conv.convRw__
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app `Ennreal.add_halves [`ε]))]
                  "]"))])))
            []
            (Tactic.abel "abel" [] [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app `h₁ [(Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₁_le_g₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁cont)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁int)])
                [])]
              "⟩")])
           [])])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app `h₂ [(Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₂_le_g₂)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂cont)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂int)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun [`x] [] "=>" («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
           ","
           (Term.app `g₁cont.add [`g₂cont])
           ","
           (Term.hole "_")]
          "⟩"))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `simple_func.coe_add)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_add)
           ","
           (Tactic.simpLemma [] [] `Pi.add_apply)]
          "]"]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))
           ","
           (Tactic.rwRule
            []
            (Term.app `lintegral_add_left [`g₁cont.measurable.coe_nnreal_ennreal]))]
          "]")
         [])
        []
        (convert "convert" [] (Term.app `add_le_add [`g₁int `g₂int]) ["using" (num "1")])
        []
        (Tactic.simp "simp" [] [] ["only"] [] [])
        []
        (Mathlib.Tactic.Conv.convLHS
         "conv_lhs"
         []
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `Ennreal.add_halves [`ε]))]
              "]"))])))
        []
        (Tactic.abel "abel" [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.abel "abel" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convLHS
       "conv_lhs"
       []
       []
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.convRw__
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Ennreal.add_halves [`ε]))]
            "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ennreal.add_halves [`ε])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.add_halves
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `add_le_add [`g₁int `g₂int]) ["using" (num "1")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_le_add [`g₁int `g₂int])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₂int
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g₁int
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_le_add
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
        [(Tactic.rwRule [] (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))
         ","
         (Tactic.rwRule [] (Term.app `lintegral_add_left [`g₁cont.measurable.coe_nnreal_ennreal]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lintegral_add_left [`g₁cont.measurable.coe_nnreal_ennreal])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₁cont.measurable.coe_nnreal_ennreal
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lintegral_add_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₁.measurable.coe_nnreal_ennreal
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lintegral_add_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `simple_func.coe_add)
         ","
         (Tactic.simpLemma [] [] `Ennreal.coe_add)
         ","
         (Tactic.simpLemma [] [] `Pi.add_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.add_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun [`x] [] "=>" («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
         ","
         (Term.app `g₁cont.add [`g₂cont])
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun [`x] [] "=>" («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
        ","
        (Term.app `g₁cont.add [`g₂cont])
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g₁cont.add [`g₂cont])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₂cont
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g₁cont.add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f₂_le_g₂ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f₂_le_g₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f₂_le_g₂ [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f₁_le_g₁ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f₁_le_g₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f₁_le_g₁ [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_le_add
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
      (Term.fun
       "fun"
       (Term.basicFun [`x] [] "=>" («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g₂ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `g₁ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app `h₂ [(Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₂_le_g₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂cont)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂int)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h₂ [(Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Ennreal.half_pos [`ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.half_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Ennreal.half_pos [`ε0]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app `h₁ [(Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₁_le_g₁)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁cont)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁int)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h₁ [(Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Ennreal.half_pos [`ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.half_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Ennreal.half_pos [`ε0]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `f
           []
           []
           ":="
           (Term.app
            `simple_func.piecewise
            [`s
             `hs
             (Term.app `simple_func.const [`α `c])
             (Term.app `simple_func.const [`α (num "0")])]))))
        []
        (Classical.«tacticBy_cases_:_»
         "by_cases"
         [`h ":"]
         («term_=_»
          (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
           "∫⁻"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           ", "
           (Term.app `f [`x])
           " ∂"
           `μ)
          "="
          (Order.BoundedOrder.«term⊤» "⊤")))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))
             ","
             (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
             ","
             `lower_semicontinuous_const
             ","
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
                   [(Tactic.simpLemma [] [] `Ennreal.top_add)
                    ","
                    (Tactic.simpLemma [] [] `le_top)
                    ","
                    (Tactic.simpLemma [] [] `h)]
                   "]"]
                  [])])))]
            "⟩"))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `simple_func.coe_const)
             ","
             (Tactic.simpLemma [] [] `simple_func.const_zero)
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_zero)
             ","
             (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
            "]"]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app `Set.indicator_le_self [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
        []
        (Classical.«tacticBy_cases_:_» "by_cases" [`hc ":"] («term_=_» `c "=" (num "0")))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
             ","
             (Term.hole "_")
             ","
             `lower_semicontinuous_const
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `hc)
               ","
               (Tactic.simpLemma [] [] `Set.indicator_zero')
               ","
               (Tactic.simpLemma [] [] `Pi.zero_apply)
               ","
               (Tactic.simpLemma [] [] `simple_func.const_zero)
               ","
               (Tactic.simpLemma [] [] `imp_true_iff)
               ","
               (Tactic.simpLemma [] [] `eq_self_iff_true)
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_zero)
               ","
               (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
               ","
               (Tactic.simpLemma [] [] `le_zero_iff)]
              "]"]
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
              [(Tactic.simpLemma [] [] `lintegral_const)
               ","
               (Tactic.simpLemma [] [] `zero_mul)
               ","
               (Tactic.simpLemma [] [] `zero_le)
               ","
               (Tactic.simpLemma [] [] `Ennreal.coe_zero)]
              "]"]
             [])])])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_<_»
              (Term.app `μ [`s])
              "<"
              («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))))]
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
                    («term_<_»
                     (Term.typeAscription
                      "("
                      (num "0")
                      ":"
                      [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                      ")")
                     "<"
                     («term_/_» `ε "/" `c)))]
                  ":="
                  (Term.app
                   (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
                   [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")]))))
               []
               (Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 []
                 []
                 ["using" (Term.app `Ennreal.add_lt_add_left [(Term.hole "_") `this])]))
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
                   [(Tactic.simpLemma [] [] `hs)
                    ","
                    (Tactic.simpLemma [] [] `hc)
                    ","
                    (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
                    ","
                    (Tactic.simpLemma [] [] `true_and_iff)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_const)
                    ","
                    (Tactic.simpLemma [] [] `Function.const_apply)
                    ","
                    (Tactic.simpLemma [] [] `lintegral_const)
                    ","
                    (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                    ","
                    (Tactic.simpLemma [] [] `Set.univ_inter)
                    ","
                    (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
                    ","
                    (Tactic.simpLemma [] [] `MeasurableSet.univ)
                    ","
                    (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.const_zero)
                    ","
                    (Tactic.simpLemma [] [] `or_false_iff)
                    ","
                    (Tactic.simpLemma [] [] `lintegral_indicator)
                    ","
                    (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
                    ","
                    (Tactic.simpLemma [] [] `Ne.def)
                    ","
                    (Tactic.simpLemma [] [] `not_false_iff)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_zero)
                    ","
                    (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                    ","
                    (Tactic.simpLemma [] [] `false_and_iff)
                    ","
                    (Tactic.simpLemma [] [] `restrict_apply)]
                   "]")]
                 ["using" `h]))]))))))
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `su)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u_open)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `μu)])
               [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders
            [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `u)] ":" (Term.hole "_") ")")
             (Lean.bracketedExplicitBinders
              "("
              [(Lean.binderIdent (Term.hole "_"))]
              ":"
              (Init.Core.«term_⊇_» `u " ⊇ " `s)
              ")")])
           ","
           («term_∧_»
            (Term.app `IsOpen [`u])
            "∧"
            («term_<_»
             (Term.app `μ [`u])
             "<"
             («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c)))))]
         [":=" [(Term.app `s.exists_is_open_lt_of_lt [(Term.hole "_") `this])]])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `Set.indicator [`u (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
           ","
           (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
           ","
           (Term.app `u_open.lower_semicontinuous_indicator [(Term.app `zero_le [(Term.hole "_")])])
           ","
           (Term.hole "_")]
          "⟩"))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `simple_func.coe_const)
             ","
             (Tactic.simpLemma [] [] `simple_func.const_zero)
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_zero)
             ","
             (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
            "]"]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `Set.indicator_le_indicator_of_subset
            [`su
             (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
             (Term.hole "_")]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            («term_≤_»
             («term_*_»
              (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
              "*"
              (Term.app `μ [`u]))
             "≤"
             («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
            (Term.byTactic'
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
                    [(Tactic.simpLemma [] [] `hs)
                     ","
                     (Tactic.simpLemma [] [] `u_open.measurable_set)
                     ","
                     (Tactic.simpLemma [] [] `simple_func.coe_const)
                     ","
                     (Tactic.simpLemma [] [] `Function.const_apply)
                     ","
                     (Tactic.simpLemma [] [] `lintegral_const)
                     ","
                     (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                     ","
                     (Tactic.simpLemma [] [] `Set.univ_inter)
                     ","
                     (Tactic.simpLemma [] [] `MeasurableSet.univ)
                     ","
                     (Tactic.simpLemma [] [] `simple_func.const_zero)
                     ","
                     (Tactic.simpLemma [] [] `lintegral_indicator)
                     ","
                     (Tactic.simpLemma [] [] `simple_func.coe_zero)
                     ","
                     (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                     ","
                     (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                     ","
                     (Tactic.simpLemma [] [] `restrict_apply)]
                    "]")]
                  []))])))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             («term_*_»
              (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
              "*"
              (Term.app `μ [`u]))
             "≤"
             («term_*_» `c "*" («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))))
            ":="
            (Term.app `Ennreal.mul_le_mul [`le_rfl `μu.le]))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.tacticSimp_rw__
                  "simp_rw"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
                   "]")
                  [])
                 []
                 (Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))]))))])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term_≤_»
           («term_*_»
            (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
            "*"
            (Term.app `μ [`u]))
           "≤"
           («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
          (Term.byTactic'
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
                  [(Tactic.simpLemma [] [] `hs)
                   ","
                   (Tactic.simpLemma [] [] `u_open.measurable_set)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_const)
                   ","
                   (Tactic.simpLemma [] [] `Function.const_apply)
                   ","
                   (Tactic.simpLemma [] [] `lintegral_const)
                   ","
                   (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                   ","
                   (Tactic.simpLemma [] [] `Set.univ_inter)
                   ","
                   (Tactic.simpLemma [] [] `MeasurableSet.univ)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.const_zero)
                   ","
                   (Tactic.simpLemma [] [] `lintegral_indicator)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_zero)
                   ","
                   (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                   ","
                   (Tactic.simpLemma [] [] `restrict_apply)]
                  "]")]
                []))])))))
        []
        (calcTactic
         "calc"
         (calcStep
          («term_≤_»
           («term_*_»
            (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
            "*"
            (Term.app `μ [`u]))
           "≤"
           («term_*_» `c "*" («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))))
          ":="
          (Term.app `Ennreal.mul_le_mul [`le_rfl `μu.le]))
         [(calcStep
           («term_=_» (Term.hole "_") "=" («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
                [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   []
                   (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
                 "]")
                [])
               []
               (Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))]))))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         («term_*_»
          (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
          "*"
          (Term.app `μ [`u]))
         "≤"
         («term_*_» `c "*" («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))))
        ":="
        (Term.app `Ennreal.mul_le_mul [`le_rfl `μu.le]))
       [(calcStep
         («term_=_» (Term.hole "_") "=" («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
               "]")
              [])
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
            "]")
           [])
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
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
          []
          (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_ne_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.mul_div_cancel'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» `c "*" (Term.app `μ [`s]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `μ [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `Ennreal.mul_le_mul [`le_rfl `μu.le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μu.le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `le_rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.mul_le_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term_*_»
        (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
        "*"
        (Term.app `μ [`u]))
       "≤"
       («term_*_» `c "*" («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `c "*" («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `μ [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
       "*"
       (Term.app `μ [`u]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `μ [`u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        («term_≤_»
         («term_*_»
          (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
          "*"
          (Term.app `μ [`u]))
         "≤"
         («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
        (Term.byTactic'
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
                [(Tactic.simpLemma [] [] `hs)
                 ","
                 (Tactic.simpLemma [] [] `u_open.measurable_set)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_const)
                 ","
                 (Tactic.simpLemma [] [] `Function.const_apply)
                 ","
                 (Tactic.simpLemma [] [] `lintegral_const)
                 ","
                 (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                 ","
                 (Tactic.simpLemma [] [] `Set.univ_inter)
                 ","
                 (Tactic.simpLemma [] [] `MeasurableSet.univ)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.const_zero)
                 ","
                 (Tactic.simpLemma [] [] `lintegral_indicator)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_zero)
                 ","
                 (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                 ","
                 (Tactic.simpLemma [] [] `restrict_apply)]
                "]")]
              []))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
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
          [(Tactic.simpLemma [] [] `hs)
           ","
           (Tactic.simpLemma [] [] `u_open.measurable_set)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_const)
           ","
           (Tactic.simpLemma [] [] `Function.const_apply)
           ","
           (Tactic.simpLemma [] [] `lintegral_const)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
           ","
           (Tactic.simpLemma [] [] `Set.univ_inter)
           ","
           (Tactic.simpLemma [] [] `MeasurableSet.univ)
           ","
           (Tactic.simpLemma [] [] `simple_func.const_zero)
           ","
           (Tactic.simpLemma [] [] `lintegral_indicator)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_zero)
           ","
           (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
           ","
           (Tactic.simpLemma [] [] `restrict_apply)]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `restrict_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_piecewise
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.piecewise_eq_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lintegral_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.const_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MeasurableSet.univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.univ_inter
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lintegral_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.const_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u_open.measurable_set
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       («term_*_»
        (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
        "*"
        (Term.app `μ [`u]))
       "≤"
       («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_*_» `c "*" (Term.app `μ [`s])) "+" `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» `c "*" (Term.app `μ [`s]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `μ [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
       "*"
       (Term.app `μ [`u]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `μ [`u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `simple_func.coe_const)
           ","
           (Tactic.simpLemma [] [] `simple_func.const_zero)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_zero)
           ","
           (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
          "]"]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `Set.indicator_le_indicator_of_subset
          [`su
           (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
           (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Set.indicator_le_indicator_of_subset
        [`su
         (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Set.indicator_le_indicator_of_subset
       [`su
        (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_le [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_le
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `su
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.indicator_le_indicator_of_subset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `simple_func.coe_const)
         ","
         (Tactic.simpLemma [] [] `simple_func.const_zero)
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_zero)
         ","
         (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_piecewise
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.piecewise_eq_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.const_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `Set.indicator [`u (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
         ","
         (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
         ","
         (Term.app `u_open.lower_semicontinuous_indicator [(Term.app `zero_le [(Term.hole "_")])])
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `Set.indicator [`u (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
        ","
        (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
        ","
        (Term.app `u_open.lower_semicontinuous_indicator [(Term.app `zero_le [(Term.hole "_")])])
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `u_open.lower_semicontinuous_indicator [(Term.app `zero_le [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_le [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `zero_le [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `u_open.lower_semicontinuous_indicator
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.indicator [`u (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.indicator
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `su)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u_open)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `μu)])
             [])]
           "⟩")])]
       [":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `u)] ":" (Term.hole "_") ")")
           (Lean.bracketedExplicitBinders
            "("
            [(Lean.binderIdent (Term.hole "_"))]
            ":"
            (Init.Core.«term_⊇_» `u " ⊇ " `s)
            ")")])
         ","
         («term_∧_»
          (Term.app `IsOpen [`u])
          "∧"
          («term_<_»
           (Term.app `μ [`u])
           "<"
           («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c)))))]
       [":=" [(Term.app `s.exists_is_open_lt_of_lt [(Term.hole "_") `this])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `s.exists_is_open_lt_of_lt [(Term.hole "_") `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `s.exists_is_open_lt_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `u)] ":" (Term.hole "_") ")")
         (Lean.bracketedExplicitBinders
          "("
          [(Lean.binderIdent (Term.hole "_"))]
          ":"
          (Init.Core.«term_⊇_» `u " ⊇ " `s)
          ")")])
       ","
       («term_∧_»
        (Term.app `IsOpen [`u])
        "∧"
        («term_<_»
         (Term.app `μ [`u])
         "<"
         («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.app `IsOpen [`u])
       "∧"
       («term_<_» (Term.app `μ [`u]) "<" («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.app `μ [`u]) "<" («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `μ [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `μ [`u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app `IsOpen [`u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 1023, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_⊇_» `u " ⊇ " `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_<_»
            (Term.app `μ [`s])
            "<"
            («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))))]
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
                  («term_<_»
                   (Term.typeAscription
                    "("
                    (num "0")
                    ":"
                    [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                    ")")
                   "<"
                   («term_/_» `ε "/" `c)))]
                ":="
                (Term.app
                 (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
                 [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")]))))
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               []
               ["using" (Term.app `Ennreal.add_lt_add_left [(Term.hole "_") `this])]))
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
                 [(Tactic.simpLemma [] [] `hs)
                  ","
                  (Tactic.simpLemma [] [] `hc)
                  ","
                  (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
                  ","
                  (Tactic.simpLemma [] [] `true_and_iff)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_const)
                  ","
                  (Tactic.simpLemma [] [] `Function.const_apply)
                  ","
                  (Tactic.simpLemma [] [] `lintegral_const)
                  ","
                  (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                  ","
                  (Tactic.simpLemma [] [] `Set.univ_inter)
                  ","
                  (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
                  ","
                  (Tactic.simpLemma [] [] `MeasurableSet.univ)
                  ","
                  (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.const_zero)
                  ","
                  (Tactic.simpLemma [] [] `or_false_iff)
                  ","
                  (Tactic.simpLemma [] [] `lintegral_indicator)
                  ","
                  (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
                  ","
                  (Tactic.simpLemma [] [] `Ne.def)
                  ","
                  (Tactic.simpLemma [] [] `not_false_iff)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_zero)
                  ","
                  (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                  ","
                  (Tactic.simpLemma [] [] `false_and_iff)
                  ","
                  (Tactic.simpLemma [] [] `restrict_apply)]
                 "]")]
               ["using" `h]))]))))))
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
               («term_<_»
                (Term.typeAscription
                 "("
                 (num "0")
                 ":"
                 [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                 ")")
                "<"
                («term_/_» `ε "/" `c)))]
             ":="
             (Term.app
              (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
              [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")]))))
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            []
            ["using" (Term.app `Ennreal.add_lt_add_left [(Term.hole "_") `this])]))
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
              [(Tactic.simpLemma [] [] `hs)
               ","
               (Tactic.simpLemma [] [] `hc)
               ","
               (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
               ","
               (Tactic.simpLemma [] [] `true_and_iff)
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_const)
               ","
               (Tactic.simpLemma [] [] `Function.const_apply)
               ","
               (Tactic.simpLemma [] [] `lintegral_const)
               ","
               (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
               ","
               (Tactic.simpLemma [] [] `Set.univ_inter)
               ","
               (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
               ","
               (Tactic.simpLemma [] [] `MeasurableSet.univ)
               ","
               (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
               ","
               (Tactic.simpLemma [] [] `simple_func.const_zero)
               ","
               (Tactic.simpLemma [] [] `or_false_iff)
               ","
               (Tactic.simpLemma [] [] `lintegral_indicator)
               ","
               (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
               ","
               (Tactic.simpLemma [] [] `Ne.def)
               ","
               (Tactic.simpLemma [] [] `not_false_iff)
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_zero)
               ","
               (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
               ","
               (Tactic.simpLemma [] [] `false_and_iff)
               ","
               (Tactic.simpLemma [] [] `restrict_apply)]
              "]")]
            ["using" `h]))])))
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
          [(Tactic.simpLemma [] [] `hs)
           ","
           (Tactic.simpLemma [] [] `hc)
           ","
           (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
           ","
           (Tactic.simpLemma [] [] `true_and_iff)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_const)
           ","
           (Tactic.simpLemma [] [] `Function.const_apply)
           ","
           (Tactic.simpLemma [] [] `lintegral_const)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
           ","
           (Tactic.simpLemma [] [] `Set.univ_inter)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
           ","
           (Tactic.simpLemma [] [] `MeasurableSet.univ)
           ","
           (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
           ","
           (Tactic.simpLemma [] [] `simple_func.const_zero)
           ","
           (Tactic.simpLemma [] [] `or_false_iff)
           ","
           (Tactic.simpLemma [] [] `lintegral_indicator)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
           ","
           (Tactic.simpLemma [] [] `Ne.def)
           ","
           (Tactic.simpLemma [] [] `not_false_iff)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_zero)
           ","
           (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
           ","
           (Tactic.simpLemma [] [] `false_and_iff)
           ","
           (Tactic.simpLemma [] [] `restrict_apply)]
          "]")]
        ["using" `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `restrict_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `false_and_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_piecewise
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.piecewise_eq_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
      `Ennreal.coe_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lintegral_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `or_false_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.const_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WithTop.mul_eq_top_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MeasurableSet.univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_ne_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.univ_inter
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lintegral_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.const_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true_and_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lt_top_iff_ne_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        []
        ["using" (Term.app `Ennreal.add_lt_add_left [(Term.hole "_") `this])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ennreal.add_lt_add_left [(Term.hole "_") `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.add_lt_add_left
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
           («term_<_»
            (Term.typeAscription "(" (num "0") ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
            "<"
            («term_/_» `ε "/" `c)))]
         ":="
         (Term.app
          (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
          [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
       [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_ne_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Ennreal.div_pos_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.typeAscription "(" (num "0") ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
       "<"
       («term_/_» `ε "/" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (num "0") ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.app `μ [`s]) "<" («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `μ [`s]) "+" («term_/_» `ε "/" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `μ [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `μ [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
           ","
           (Term.hole "_")
           ","
           `lower_semicontinuous_const
           ","
           (Term.hole "_")]
          "⟩"))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `hc)
             ","
             (Tactic.simpLemma [] [] `Set.indicator_zero')
             ","
             (Tactic.simpLemma [] [] `Pi.zero_apply)
             ","
             (Tactic.simpLemma [] [] `simple_func.const_zero)
             ","
             (Tactic.simpLemma [] [] `imp_true_iff)
             ","
             (Tactic.simpLemma [] [] `eq_self_iff_true)
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_zero)
             ","
             (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
             ","
             (Tactic.simpLemma [] [] `le_zero_iff)]
            "]"]
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
            [(Tactic.simpLemma [] [] `lintegral_const)
             ","
             (Tactic.simpLemma [] [] `zero_mul)
             ","
             (Tactic.simpLemma [] [] `zero_le)
             ","
             (Tactic.simpLemma [] [] `Ennreal.coe_zero)]
            "]"]
           [])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `lintegral_const)
           ","
           (Tactic.simpLemma [] [] `zero_mul)
           ","
           (Tactic.simpLemma [] [] `zero_le)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_zero)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `lintegral_const)
         ","
         (Tactic.simpLemma [] [] `zero_mul)
         ","
         (Tactic.simpLemma [] [] `zero_le)
         ","
         (Tactic.simpLemma [] [] `Ennreal.coe_zero)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lintegral_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `hc)
           ","
           (Tactic.simpLemma [] [] `Set.indicator_zero')
           ","
           (Tactic.simpLemma [] [] `Pi.zero_apply)
           ","
           (Tactic.simpLemma [] [] `simple_func.const_zero)
           ","
           (Tactic.simpLemma [] [] `imp_true_iff)
           ","
           (Tactic.simpLemma [] [] `eq_self_iff_true)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_zero)
           ","
           (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
           ","
           (Tactic.simpLemma [] [] `le_zero_iff)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `hc)
         ","
         (Tactic.simpLemma [] [] `Set.indicator_zero')
         ","
         (Tactic.simpLemma [] [] `Pi.zero_apply)
         ","
         (Tactic.simpLemma [] [] `simple_func.const_zero)
         ","
         (Tactic.simpLemma [] [] `imp_true_iff)
         ","
         (Tactic.simpLemma [] [] `eq_self_iff_true)
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_zero)
         ","
         (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
         ","
         (Tactic.simpLemma [] [] `le_zero_iff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_zero_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_piecewise
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.piecewise_eq_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_self_iff_true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `imp_true_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.const_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.zero_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.indicator_zero'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
         ","
         (Term.hole "_")
         ","
         `lower_semicontinuous_const
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
        ","
        (Term.hole "_")
        ","
        `lower_semicontinuous_const
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lower_semicontinuous_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`hc ":"] («term_=_» `c "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `c "=" (num "0"))
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
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))
           ","
           (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
           ","
           `lower_semicontinuous_const
           ","
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
                 [(Tactic.simpLemma [] [] `Ennreal.top_add)
                  ","
                  (Tactic.simpLemma [] [] `le_top)
                  ","
                  (Tactic.simpLemma [] [] `h)]
                 "]"]
                [])])))]
          "⟩"))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `simple_func.coe_const)
           ","
           (Tactic.simpLemma [] [] `simple_func.const_zero)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_zero)
           ","
           (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
          "]"]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app `Set.indicator_le_self [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `Set.indicator_le_self [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.indicator_le_self [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.indicator_le_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `simple_func.coe_const)
         ","
         (Tactic.simpLemma [] [] `simple_func.const_zero)
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_zero)
         ","
         (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_piecewise
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.piecewise_eq_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.const_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))
         ","
         (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
         ","
         `lower_semicontinuous_const
         ","
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
               [(Tactic.simpLemma [] [] `Ennreal.top_add)
                ","
                (Tactic.simpLemma [] [] `le_top)
                ","
                (Tactic.simpLemma [] [] `h)]
               "]"]
              [])])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))
        ","
        (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
        ","
        `lower_semicontinuous_const
        ","
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
              [(Tactic.simpLemma [] [] `Ennreal.top_add)
               ","
               (Tactic.simpLemma [] [] `le_top)
               ","
               (Tactic.simpLemma [] [] `h)]
              "]"]
             [])])))]
       "⟩")
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
            [(Tactic.simpLemma [] [] `Ennreal.top_add)
             ","
             (Tactic.simpLemma [] [] `le_top)
             ","
             (Tactic.simpLemma [] [] `h)]
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
        [(Tactic.simpLemma [] [] `Ennreal.top_add)
         ","
         (Tactic.simpLemma [] [] `le_top)
         ","
         (Tactic.simpLemma [] [] `h)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.top_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lower_semicontinuous_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_»
       "by_cases"
       [`h ":"]
       («term_=_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `f [`x])
         " ∂"
         `μ)
        "="
        (Order.BoundedOrder.«term⊤» "⊤")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `f [`x])
        " ∂"
        `μ)
       "="
       (Order.BoundedOrder.«term⊤» "⊤"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `f [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `f [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `f
         []
         []
         ":="
         (Term.app
          `simple_func.piecewise
          [`s
           `hs
           (Term.app `simple_func.const [`α `c])
           (Term.app `simple_func.const [`α (num "0")])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `simple_func.piecewise
       [`s `hs (Term.app `simple_func.const [`α `c]) (Term.app `simple_func.const [`α (num "0")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `simple_func.const [`α (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simple_func.const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `simple_func.const [`α (num "0")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `simple_func.const [`α `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simple_func.const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `simple_func.const [`α `c])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simple_func.piecewise
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `f)]
       ["using" `MeasureTheory.SimpleFunc.induction]
       ["with"
        [(Lean.binderIdent `c)
         (Lean.binderIdent `s)
         (Lean.binderIdent `hs)
         (Lean.binderIdent `f₁)
         (Lean.binderIdent `f₂)
         (Lean.binderIdent `H)
         (Lean.binderIdent `h₁)
         (Lean.binderIdent `h₂)]]
       ["generalizing" [`ε]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `g)]
         [":" (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
       ","
       («term_∧_»
        (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `f [`x]) "≤" (Term.app `g [`x])))
        "∧"
        («term_∧_»
         (Term.app `LowerSemicontinuous [`g])
         "∧"
         («term_≤_»
          (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
           "∫⁻"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           ", "
           (Term.app `g [`x])
           " ∂"
           `μ)
          "≤"
          («term_+_»
           (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
            "∫⁻"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
            ", "
            (Term.app `f [`x])
            " ∂"
            `μ)
           "+"
           `ε)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `f [`x]) "≤" (Term.app `g [`x])))
       "∧"
       («term_∧_»
        (Term.app `LowerSemicontinuous [`g])
        "∧"
        («term_≤_»
         (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
          "∫⁻"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app `g [`x])
          " ∂"
          `μ)
         "≤"
         («term_+_»
          (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
           "∫⁻"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           ", "
           (Term.app `f [`x])
           " ∂"
           `μ)
          "+"
          `ε))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.app `LowerSemicontinuous [`g])
       "∧"
       («term_≤_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `g [`x])
         " ∂"
         `μ)
        "≤"
        («term_+_»
         (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
          "∫⁻"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app `f [`x])
          " ∂"
          `μ)
         "+"
         `ε)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `g [`x])
        " ∂"
        `μ)
       "≤"
       («term_+_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `f [`x])
         " ∂"
         `μ)
        "+"
        `ε))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `f [`x])
        " ∂"
        `μ)
       "+"
       `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `f [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `f [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `g [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `g [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app `LowerSemicontinuous [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LowerSemicontinuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 1023, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `f [`x]) "≤" (Term.app `g [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.app `f [`x]) "≤" (Term.app `g [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 0, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `f [`x]) "≤" (Term.app `g [`x])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `ε "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»
       `α
       " →ₛ "
       (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»', expected 'MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.term_→ₛ_._@.MeasureTheory.Integral.VitaliCaratheodory._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given a simple function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
    function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
    `lintegral`.
    Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
  theorem
    SimpleFunc.exists_le_lower_semicontinuous_lintegral_ge
    ( f : α →ₛ ℝ≥0 ) { ε : ℝ≥0∞ } ( ε0 : ε ≠ 0 )
      :
        ∃
          g : α → ℝ≥0
          ,
          ∀ x , f x ≤ g x ∧ LowerSemicontinuous g ∧ ∫⁻ x , g x ∂ μ ≤ ∫⁻ x , f x ∂ μ + ε
    :=
      by
        induction'
            f
            using MeasureTheory.SimpleFunc.induction
            with c s hs f₁ f₂ H h₁ h₂
            generalizing ε
          ·
            let f := simple_func.piecewise s hs simple_func.const α c simple_func.const α 0
              by_cases h : ∫⁻ x , f x ∂ μ = ⊤
              ·
                refine'
                    ⟨
                      fun x => c
                        ,
                        fun x => _
                        ,
                        lower_semicontinuous_const
                        ,
                        by simp only [ Ennreal.top_add , le_top , h ]
                      ⟩
                  simp
                    only
                    [
                      simple_func.coe_const
                        ,
                        simple_func.const_zero
                        ,
                        simple_func.coe_zero
                        ,
                        Set.piecewise_eq_indicator
                        ,
                        simple_func.coe_piecewise
                      ]
                  exact Set.indicator_le_self _ _ _
              by_cases hc : c = 0
              ·
                refine' ⟨ fun x => 0 , _ , lower_semicontinuous_const , _ ⟩
                  ·
                    simp
                      only
                      [
                        hc
                          ,
                          Set.indicator_zero'
                          ,
                          Pi.zero_apply
                          ,
                          simple_func.const_zero
                          ,
                          imp_true_iff
                          ,
                          eq_self_iff_true
                          ,
                          simple_func.coe_zero
                          ,
                          Set.piecewise_eq_indicator
                          ,
                          simple_func.coe_piecewise
                          ,
                          le_zero_iff
                        ]
                  · simp only [ lintegral_const , zero_mul , zero_le , Ennreal.coe_zero ]
              have
                : μ s < μ s + ε / c
                  :=
                  by
                    have
                        : ( 0 : ℝ≥0∞ ) < ε / c
                          :=
                          Ennreal.div_pos_iff . 2 ⟨ ε0 , Ennreal.coe_ne_top ⟩
                      simpa using Ennreal.add_lt_add_left _ this
                      simpa
                        only
                          [
                            hs
                              ,
                              hc
                              ,
                              lt_top_iff_ne_top
                              ,
                              true_and_iff
                              ,
                              simple_func.coe_const
                              ,
                              Function.const_apply
                              ,
                              lintegral_const
                              ,
                              Ennreal.coe_indicator
                              ,
                              Set.univ_inter
                              ,
                              Ennreal.coe_ne_top
                              ,
                              MeasurableSet.univ
                              ,
                              WithTop.mul_eq_top_iff
                              ,
                              simple_func.const_zero
                              ,
                              or_false_iff
                              ,
                              lintegral_indicator
                              ,
                              Ennreal.coe_eq_zero
                              ,
                              Ne.def
                              ,
                              not_false_iff
                              ,
                              simple_func.coe_zero
                              ,
                              Set.piecewise_eq_indicator
                              ,
                              simple_func.coe_piecewise
                              ,
                              false_and_iff
                              ,
                              restrict_apply
                            ]
                          using h
              obtain
                ⟨ u , su , u_open , μu ⟩
                : ∃ ( u : _ ) ( _ : u ⊇ s ) , IsOpen u ∧ μ u < μ s + ε / c
                := s.exists_is_open_lt_of_lt _ this
              refine'
                ⟨
                  Set.indicator u fun x => c
                    ,
                    fun x => _
                    ,
                    u_open.lower_semicontinuous_indicator zero_le _
                    ,
                    _
                  ⟩
              ·
                simp
                    only
                    [
                      simple_func.coe_const
                        ,
                        simple_func.const_zero
                        ,
                        simple_func.coe_zero
                        ,
                        Set.piecewise_eq_indicator
                        ,
                        simple_func.coe_piecewise
                      ]
                  exact Set.indicator_le_indicator_of_subset su fun x => zero_le _ _
              ·
                suffices
                    ( c : ℝ≥0∞ ) * μ u ≤ c * μ s + ε
                      by
                        simpa
                          only
                            [
                              hs
                                ,
                                u_open.measurable_set
                                ,
                                simple_func.coe_const
                                ,
                                Function.const_apply
                                ,
                                lintegral_const
                                ,
                                Ennreal.coe_indicator
                                ,
                                Set.univ_inter
                                ,
                                MeasurableSet.univ
                                ,
                                simple_func.const_zero
                                ,
                                lintegral_indicator
                                ,
                                simple_func.coe_zero
                                ,
                                Set.piecewise_eq_indicator
                                ,
                                simple_func.coe_piecewise
                                ,
                                restrict_apply
                              ]
                  calc
                    ( c : ℝ≥0∞ ) * μ u ≤ c * μ s + ε / c := Ennreal.mul_le_mul le_rfl μu.le
                    _ = c * μ s + ε
                      :=
                      by
                        simp_rw [ mul_add ]
                          rw [ Ennreal.mul_div_cancel' _ Ennreal.coe_ne_top ]
                          simpa using hc
          ·
            rcases h₁ Ennreal.half_pos ε0 . ne' with ⟨ g₁ , f₁_le_g₁ , g₁cont , g₁int ⟩
              rcases h₂ Ennreal.half_pos ε0 . ne' with ⟨ g₂ , f₂_le_g₂ , g₂cont , g₂int ⟩
              refine'
                ⟨
                  fun x => g₁ x + g₂ x
                    ,
                    fun x => add_le_add f₁_le_g₁ x f₂_le_g₂ x
                    ,
                    g₁cont.add g₂cont
                    ,
                    _
                  ⟩
              simp only [ simple_func.coe_add , Ennreal.coe_add , Pi.add_apply ]
              rw
                [
                  lintegral_add_left f₁.measurable.coe_nnreal_ennreal
                    ,
                    lintegral_add_left g₁cont.measurable.coe_nnreal_ennreal
                  ]
              convert add_le_add g₁int g₂int using 1
              simp only
              conv_lhs => rw [ ← Ennreal.add_halves ε ]
              abel
#align
  measure_theory.simple_func.exists_le_lower_semicontinuous_lintegral_ge MeasureTheory.SimpleFunc.exists_le_lower_semicontinuous_lintegral_ge

open SimpleFunc (eapproxDiff tsum_eapprox_diff)

/-- Given a measurable function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_le_lower_semicontinuous_lintegral_ge (f : α → ℝ≥0∞) (hf : Measurable f) {ε : ℝ≥0∞}
    (εpos : ε ≠ 0) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, f x ≤ g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε :=
  by
  rcases Ennreal.exists_pos_sum_of_countable' εpos ℕ with ⟨δ, δpos, hδ⟩
  have :
    ∀ n,
      ∃ g : α → ℝ≥0,
        (∀ x, simple_func.eapprox_diff f n x ≤ g x) ∧
          LowerSemicontinuous g ∧
            (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, simple_func.eapprox_diff f n x ∂μ) + δ n :=
    fun n =>
    simple_func.exists_le_lower_semicontinuous_lintegral_ge μ (simple_func.eapprox_diff f n)
      (δpos n).ne'
  choose g f_le_g gcont hg using this
  refine' ⟨fun x => ∑' n, g n x, fun x => _, _, _⟩
  · rw [← tsum_eapprox_diff f hf]
    exact Ennreal.tsum_le_tsum fun n => Ennreal.coe_le_coe.2 (f_le_g n x)
  · apply lower_semicontinuous_tsum fun n => _
    exact
      ennreal.continuous_coe.comp_lower_semicontinuous (gcont n) fun x y hxy =>
        Ennreal.coe_le_coe.2 hxy
  ·
    calc
      (∫⁻ x, ∑' n : ℕ, g n x ∂μ) = ∑' n, ∫⁻ x, g n x ∂μ := by
        rw [lintegral_tsum fun n => (gcont n).Measurable.coe_nnreal_ennreal.AeMeasurable]
      _ ≤ ∑' n, (∫⁻ x, eapprox_diff f n x ∂μ) + δ n := Ennreal.tsum_le_tsum hg
      _ = (∑' n, ∫⁻ x, eapprox_diff f n x ∂μ) + ∑' n, δ n := Ennreal.tsum_add
      _ ≤ (∫⁻ x : α, f x ∂μ) + ε := by
        refine' add_le_add _ hδ.le
        rw [← lintegral_tsum]
        · simp_rw [tsum_eapprox_diff f hf, le_refl]
        · intro n
          exact (simple_func.measurable _).coe_nnreal_ennreal.AeMeasurable
      
#align
  measure_theory.exists_le_lower_semicontinuous_lintegral_ge MeasureTheory.exists_le_lower_semicontinuous_lintegral_ge

/-- Given a measurable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_lt_lower_semicontinuous_lintegral_ge [SigmaFinite μ] (f : α → ℝ≥0)
    (fmeas : Measurable f) {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, (f x : ℝ≥0∞) < g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε :=
  by
  have : ε / 2 ≠ 0 := (Ennreal.half_pos ε0).ne'
  rcases exists_pos_lintegral_lt_of_sigma_finite μ this with ⟨w, wpos, wmeas, wint⟩
  let f' x := ((f x + w x : ℝ≥0) : ℝ≥0∞)
  rcases exists_le_lower_semicontinuous_lintegral_ge μ f' (fmeas.add wmeas).coe_nnreal_ennreal
      this with
    ⟨g, le_g, gcont, gint⟩
  refine' ⟨g, fun x => _, gcont, _⟩
  ·
    calc
      (f x : ℝ≥0∞) < f' x := by simpa [← Ennreal.coe_lt_coe] using add_lt_add_left (wpos x) (f x)
      _ ≤ g x := le_g x
      
  ·
    calc
      (∫⁻ x : α, g x ∂μ) ≤ (∫⁻ x : α, f x + w x ∂μ) + ε / 2 := gint
      _ = ((∫⁻ x : α, f x ∂μ) + ∫⁻ x : α, w x ∂μ) + ε / 2 := by
        rw [lintegral_add_right _ wmeas.coe_nnreal_ennreal]
      _ ≤ (∫⁻ x : α, f x ∂μ) + ε / 2 + ε / 2 := add_le_add_right (add_le_add_left wint.le _) _
      _ = (∫⁻ x : α, f x ∂μ) + ε := by rw [add_assoc, Ennreal.add_halves]
      
#align
  measure_theory.exists_lt_lower_semicontinuous_lintegral_ge MeasureTheory.exists_lt_lower_semicontinuous_lintegral_ge

/-- Given an almost everywhere measurable function `f` with values in `ℝ≥0` in a sigma-finite space,
there exists a lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable [SigmaFinite μ] (f : α → ℝ≥0)
    (fmeas : AeMeasurable f μ) {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, (f x : ℝ≥0∞) < g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε :=
  by
  have : ε / 2 ≠ 0 := (Ennreal.half_pos ε0).ne'
  rcases exists_lt_lower_semicontinuous_lintegral_ge μ (fmeas.mk f) fmeas.measurable_mk this with
    ⟨g0, f_lt_g0, g0_cont, g0_int⟩
  rcases exists_measurable_superset_of_null fmeas.ae_eq_mk with ⟨s, hs, smeas, μs⟩
  rcases exists_le_lower_semicontinuous_lintegral_ge μ (s.indicator fun x => ∞)
      (measurable_const.indicator smeas) this with
    ⟨g1, le_g1, g1_cont, g1_int⟩
  refine' ⟨fun x => g0 x + g1 x, fun x => _, g0_cont.add g1_cont, _⟩
  · by_cases h : x ∈ s
    · have := le_g1 x
      simp only [h, Set.indicator_of_mem, top_le_iff] at this
      simp [this]
    · have : f x = fmeas.mk f x := by
        rw [Set.compl_subset_comm] at hs
        exact hs h
      rw [this]
      exact (f_lt_g0 x).trans_le le_self_add
  ·
    calc
      (∫⁻ x, g0 x + g1 x ∂μ) = (∫⁻ x, g0 x ∂μ) + ∫⁻ x, g1 x ∂μ :=
        lintegral_add_left g0_cont.measurable _
      _ ≤ (∫⁻ x, f x ∂μ) + ε / 2 + (0 + ε / 2) :=
        by
        refine' add_le_add _ _
        · convert g0_int using 2
          exact lintegral_congr_ae (fmeas.ae_eq_mk.fun_comp _)
        · convert g1_int
          simp only [smeas, μs, lintegral_const, Set.univ_inter, MeasurableSet.univ,
            lintegral_indicator, mul_zero, restrict_apply]
      _ = (∫⁻ x, f x ∂μ) + ε := by simp only [add_assoc, Ennreal.add_halves, zero_add]
      
#align
  measure_theory.exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable MeasureTheory.exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable

variable {μ}

/-- Given an integrable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_lt_lower_semicontinuous_integral_gt_nnreal [SigmaFinite μ] (f : α → ℝ≥0)
    (fint : Integrable (fun x => (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, (f x : ℝ≥0∞) < g x) ∧
        LowerSemicontinuous g ∧
          (∀ᵐ x ∂μ, g x < ⊤) ∧
            Integrable (fun x => (g x).toReal) μ ∧ (∫ x, (g x).toReal ∂μ) < (∫ x, f x ∂μ) + ε :=
  by
  have fmeas : AeMeasurable f μ :=
    by
    convert fint.ae_strongly_measurable.real_to_nnreal.ae_measurable
    ext1 x
    simp only [Real.to_nnreal_coe]
  lift ε to ℝ≥0 using εpos.le
  obtain ⟨δ, δpos, hδε⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ δ < ε
  exact exists_between εpos
  have int_f_ne_top : (∫⁻ a : α, f a ∂μ) ≠ ∞ :=
    (has_finite_integral_iff_of_nnreal.1 fint.has_finite_integral).Ne
  rcases exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable μ f fmeas
      (Ennreal.coe_ne_zero.2 δpos.ne') with
    ⟨g, f_lt_g, gcont, gint⟩
  have gint_ne : (∫⁻ x : α, g x ∂μ) ≠ ∞ := ne_top_of_le_ne_top (by simpa) gint
  have g_lt_top : ∀ᵐ x : α ∂μ, g x < ∞ := ae_lt_top gcont.measurable gint_ne
  have Ig : (∫⁻ a : α, Ennreal.ofReal (g a).toReal ∂μ) = ∫⁻ a : α, g a ∂μ :=
    by
    apply lintegral_congr_ae
    filter_upwards [g_lt_top] with _ hx
    simp only [hx.ne, Ennreal.of_real_to_real, Ne.def, not_false_iff]
  refine' ⟨g, f_lt_g, gcont, g_lt_top, _, _⟩
  · refine' ⟨gcont.measurable.ennreal_to_real.ae_measurable.ae_strongly_measurable, _⟩
    simp only [has_finite_integral_iff_norm, Real.norm_eq_abs, abs_of_nonneg Ennreal.to_real_nonneg]
    convert gint_ne.lt_top using 1
  · rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
    ·
      calc
        Ennreal.toReal (∫⁻ a : α, Ennreal.ofReal (g a).toReal ∂μ) =
            Ennreal.toReal (∫⁻ a : α, g a ∂μ) :=
          by congr 1
        _ ≤ Ennreal.toReal ((∫⁻ a : α, f a ∂μ) + δ) :=
          by
          apply Ennreal.to_real_mono _ gint
          simpa using int_f_ne_top
        _ = Ennreal.toReal (∫⁻ a : α, f a ∂μ) + δ := by
          rw [Ennreal.to_real_add int_f_ne_top Ennreal.coe_ne_top, Ennreal.coe_to_real]
        _ < Ennreal.toReal (∫⁻ a : α, f a ∂μ) + ε := add_lt_add_left hδε _
        _ = (∫⁻ a : α, Ennreal.ofReal ↑(f a) ∂μ).toReal + ε := by simp
        
    · apply Filter.eventually_of_forall fun x => _
      simp
    · exact fmeas.coe_nnreal_real.ae_strongly_measurable
    · apply Filter.eventually_of_forall fun x => _
      simp
    · apply gcont.measurable.ennreal_to_real.ae_measurable.ae_strongly_measurable
#align
  measure_theory.exists_lt_lower_semicontinuous_integral_gt_nnreal MeasureTheory.exists_lt_lower_semicontinuous_integral_gt_nnreal

/-! ### Upper semicontinuous lower bound for nonnegative functions -/


/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (F «expr ⊆ » s) -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given a simple function `f` with values in `ℝ≥0`, there exists an upper semicontinuous\nfunction `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of\n`lintegral`.\nAuxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `SimpleFunc.exists_upper_semicontinuous_le_lintegral_le [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»
           `α
           " →ₛ "
           (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`int_f]
         [":"
          («term_≠_»
           (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
            "∫⁻"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
            ", "
            (Term.app `f [`x])
            " ∂"
            `μ)
           "≠"
           (Ennreal.Data.Real.Ennreal.ennreal.top "∞"))]
         []
         ")")
        (Term.implicitBinder "{" [`ε] [":" (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] "}")
        (Term.explicitBinder "(" [`ε0] [":" («term_≠_» `ε "≠" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `g)]
           [":" (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
         ","
         («term_∧_»
          (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `f [`x])))
          "∧"
          («term_∧_»
           (Term.app `UpperSemicontinuous [`g])
           "∧"
           («term_≤_»
            (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
             "∫⁻"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             ", "
             (Term.app `f [`x])
             " ∂"
             `μ)
            "≤"
            («term_+_»
             (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
              "∫⁻"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
              ", "
              (Term.app `g [`x])
              " ∂"
              `μ)
             "+"
             `ε)))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `f)]
            ["using" `MeasureTheory.SimpleFunc.induction]
            ["with"
             [(Lean.binderIdent `c)
              (Lean.binderIdent `s)
              (Lean.binderIdent `hs)
              (Lean.binderIdent `f₁)
              (Lean.binderIdent `f₂)
              (Lean.binderIdent `H)
              (Lean.binderIdent `h₁)
              (Lean.binderIdent `h₂)]]
            ["generalizing" [`ε]])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `f
                []
                []
                ":="
                (Term.app
                 `simple_func.piecewise
                 [`s
                  `hs
                  (Term.app `simple_func.const [`α `c])
                  (Term.app `simple_func.const [`α (num "0")])]))))
             []
             (Classical.«tacticBy_cases_:_» "by_cases" [`hc ":"] («term_=_» `c "=" (num "0")))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
                  ","
                  (Term.hole "_")
                  ","
                  `upper_semicontinuous_const
                  ","
                  (Term.hole "_")]
                 "⟩"))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `hc)
                    ","
                    (Tactic.simpLemma [] [] `Set.indicator_zero')
                    ","
                    (Tactic.simpLemma [] [] `Pi.zero_apply)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.const_zero)
                    ","
                    (Tactic.simpLemma [] [] `imp_true_iff)
                    ","
                    (Tactic.simpLemma [] [] `eq_self_iff_true)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_zero)
                    ","
                    (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                    ","
                    (Tactic.simpLemma [] [] `le_zero_iff)]
                   "]"]
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
                   [(Tactic.simpLemma [] [] `hc)
                    ","
                    (Tactic.simpLemma [] [] `Set.indicator_zero')
                    ","
                    (Tactic.simpLemma [] [] `lintegral_const)
                    ","
                    (Tactic.simpLemma [] [] `zero_mul)
                    ","
                    (Tactic.simpLemma [] [] `Pi.zero_apply)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.const_zero)
                    ","
                    (Tactic.simpLemma [] [] `zero_add)
                    ","
                    (Tactic.simpLemma [] [] `zero_le')
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_zero)
                    ","
                    (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                    ","
                    (Tactic.simpLemma [] [] `Ennreal.coe_zero)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                    ","
                    (Tactic.simpLemma [] [] `zero_le)]
                   "]"]
                  [])])])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`μs_lt_top []]
                [(Term.typeSpec
                  ":"
                  («term_<_» (Term.app `μ [`s]) "<" (Ennreal.Data.Real.Ennreal.ennreal.top "∞")))]
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
                        [(Tactic.simpLemma [] [] `hs)
                         ","
                         (Tactic.simpLemma [] [] `hc)
                         ","
                         (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
                         ","
                         (Tactic.simpLemma [] [] `true_and_iff)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_const)
                         ","
                         (Tactic.simpLemma [] [] `or_false_iff)
                         ","
                         (Tactic.simpLemma [] [] `lintegral_const)
                         ","
                         (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                         ","
                         (Tactic.simpLemma [] [] `Set.univ_inter)
                         ","
                         (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
                         ","
                         (Tactic.simpLemma [] [] (Term.app `restrict_apply [`MeasurableSet.univ]))
                         ","
                         (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.const_zero)
                         ","
                         (Tactic.simpLemma [] [] `Function.const_apply)
                         ","
                         (Tactic.simpLemma [] [] `lintegral_indicator)
                         ","
                         (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
                         ","
                         (Tactic.simpLemma [] [] `Ne.def)
                         ","
                         (Tactic.simpLemma [] [] `not_false_iff)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_zero)
                         ","
                         (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                         ","
                         (Tactic.simpLemma [] [] `false_and_iff)]
                        "]")]
                      ["using" `int_f]))]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_<_»
                   (Term.typeAscription
                    "("
                    (num "0")
                    ":"
                    [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                    ")")
                   "<"
                   («term_/_» `ε "/" `c)))]
                ":="
                (Term.app
                 (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
                 [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")]))))
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `F)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Fs)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `F_closed)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `μF)])
                    [])]
                  "⟩")])]
              [":"
               («term∃_,_»
                "∃"
                (Lean.explicitBinders
                 [(Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent `F)]
                   ":"
                   (Term.hole "_")
                   ")")
                  (Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent (Term.hole "_"))]
                   ":"
                   («term_⊆_» `F "⊆" `s)
                   ")")])
                ","
                («term_∧_»
                 (Term.app `IsClosed [`F])
                 "∧"
                 («term_<_»
                  (Term.app `μ [`s])
                  "<"
                  («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c)))))]
              [":=" [(Term.app `hs.exists_is_closed_lt_add [`μs_lt_top.ne `this.ne'])]])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.app `Set.indicator [`F (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
                ","
                (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
                ","
                (Term.app
                 `F_closed.upper_semicontinuous_indicator
                 [(Term.app `zero_le [(Term.hole "_")])])
                ","
                (Term.hole "_")]
               "⟩"))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `simple_func.coe_const)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.const_zero)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_zero)
                  ","
                  (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
                 "]"]
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `Set.indicator_le_indicator_of_subset
                 [`Fs
                  (Term.fun
                   "fun"
                   (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
                  (Term.hole "_")]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.tacticSuffices_
                "suffices"
                (Term.sufficesDecl
                 []
                 («term_≤_»
                  («term_*_»
                   (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
                   "*"
                   (Term.app `μ [`s]))
                  "≤"
                  («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
                 (Term.byTactic'
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
                         [(Tactic.simpLemma [] [] `hs)
                          ","
                          (Tactic.simpLemma [] [] `F_closed.measurable_set)
                          ","
                          (Tactic.simpLemma [] [] `simple_func.coe_const)
                          ","
                          (Tactic.simpLemma [] [] `Function.const_apply)
                          ","
                          (Tactic.simpLemma [] [] `lintegral_const)
                          ","
                          (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                          ","
                          (Tactic.simpLemma [] [] `Set.univ_inter)
                          ","
                          (Tactic.simpLemma [] [] `MeasurableSet.univ)
                          ","
                          (Tactic.simpLemma [] [] `simple_func.const_zero)
                          ","
                          (Tactic.simpLemma [] [] `lintegral_indicator)
                          ","
                          (Tactic.simpLemma [] [] `simple_func.coe_zero)
                          ","
                          (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                          ","
                          (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                          ","
                          (Tactic.simpLemma [] [] `restrict_apply)]
                         "]")]
                       []))])))))
               []
               (calcTactic
                "calc"
                (calcStep
                 («term_≤_»
                  («term_*_»
                   (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
                   "*"
                   (Term.app `μ [`s]))
                  "≤"
                  («term_*_» `c "*" («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c))))
                 ":="
                 (Term.app `Ennreal.mul_le_mul [`le_rfl `μF.le]))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Mathlib.Tactic.tacticSimp_rw__
                       "simp_rw"
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
                       [])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule
                          []
                          (Term.app
                           `Ennreal.mul_div_cancel'
                           [(Term.hole "_") `Ennreal.coe_ne_top]))]
                        "]")
                       [])
                      []
                      (Std.Tactic.Simpa.simpa
                       "simpa"
                       []
                       []
                       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))]))))])])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`A []]
                [(Term.typeSpec
                  ":"
                  («term_≠_»
                   («term_+_»
                    (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                     "∫⁻"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                     ", "
                     (Term.app `f₁ [`x])
                     " ∂"
                     `μ)
                    "+"
                    (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                     "∫⁻"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                     ", "
                     (Term.app `f₂ [`x])
                     " ∂"
                     `μ))
                   "≠"
                   (Order.BoundedOrder.«term⊤» "⊤")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.tacticRwa__
                     "rwa"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))]
                      "]")
                     [])]))))))
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 `h₁
                 [(Term.proj
                   (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
                   "."
                   (fieldIdx "1"))
                  (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₁_le_g₁)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁cont)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁int)])
                     [])]
                   "⟩")])
                [])])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 `h₂
                 [(Term.proj
                   (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
                   "."
                   (fieldIdx "2"))
                  (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₂_le_g₂)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂cont)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂int)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`x]
                  []
                  "=>"
                  («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`x]
                  []
                  "=>"
                  (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
                ","
                (Term.app `g₁cont.add [`g₂cont])
                ","
                (Term.hole "_")]
               "⟩"))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `simple_func.coe_add)
                ","
                (Tactic.simpLemma [] [] `Ennreal.coe_add)
                ","
                (Tactic.simpLemma [] [] `Pi.add_apply)]
               "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))
                ","
                (Tactic.rwRule
                 []
                 (Term.app `lintegral_add_left [`g₁cont.measurable.coe_nnreal_ennreal]))]
               "]")
              [])
             []
             (convert "convert" [] (Term.app `add_le_add [`g₁int `g₂int]) ["using" (num "1")])
             []
             (Tactic.simp "simp" [] [] ["only"] [] [])
             []
             (Mathlib.Tactic.Conv.convLHS
              "conv_lhs"
              []
              []
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(Tactic.Conv.convRw__
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `Ennreal.add_halves [`ε]))]
                   "]"))])))
             []
             (Tactic.abel "abel" [] [])])])))
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
         [(Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `f)]
           ["using" `MeasureTheory.SimpleFunc.induction]
           ["with"
            [(Lean.binderIdent `c)
             (Lean.binderIdent `s)
             (Lean.binderIdent `hs)
             (Lean.binderIdent `f₁)
             (Lean.binderIdent `f₂)
             (Lean.binderIdent `H)
             (Lean.binderIdent `h₁)
             (Lean.binderIdent `h₂)]]
           ["generalizing" [`ε]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `f
               []
               []
               ":="
               (Term.app
                `simple_func.piecewise
                [`s
                 `hs
                 (Term.app `simple_func.const [`α `c])
                 (Term.app `simple_func.const [`α (num "0")])]))))
            []
            (Classical.«tacticBy_cases_:_» "by_cases" [`hc ":"] («term_=_» `c "=" (num "0")))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
                 ","
                 (Term.hole "_")
                 ","
                 `upper_semicontinuous_const
                 ","
                 (Term.hole "_")]
                "⟩"))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `hc)
                   ","
                   (Tactic.simpLemma [] [] `Set.indicator_zero')
                   ","
                   (Tactic.simpLemma [] [] `Pi.zero_apply)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.const_zero)
                   ","
                   (Tactic.simpLemma [] [] `imp_true_iff)
                   ","
                   (Tactic.simpLemma [] [] `eq_self_iff_true)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_zero)
                   ","
                   (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                   ","
                   (Tactic.simpLemma [] [] `le_zero_iff)]
                  "]"]
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
                  [(Tactic.simpLemma [] [] `hc)
                   ","
                   (Tactic.simpLemma [] [] `Set.indicator_zero')
                   ","
                   (Tactic.simpLemma [] [] `lintegral_const)
                   ","
                   (Tactic.simpLemma [] [] `zero_mul)
                   ","
                   (Tactic.simpLemma [] [] `Pi.zero_apply)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.const_zero)
                   ","
                   (Tactic.simpLemma [] [] `zero_add)
                   ","
                   (Tactic.simpLemma [] [] `zero_le')
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_zero)
                   ","
                   (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                   ","
                   (Tactic.simpLemma [] [] `Ennreal.coe_zero)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                   ","
                   (Tactic.simpLemma [] [] `zero_le)]
                  "]"]
                 [])])])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`μs_lt_top []]
               [(Term.typeSpec
                 ":"
                 («term_<_» (Term.app `μ [`s]) "<" (Ennreal.Data.Real.Ennreal.ennreal.top "∞")))]
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
                       [(Tactic.simpLemma [] [] `hs)
                        ","
                        (Tactic.simpLemma [] [] `hc)
                        ","
                        (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
                        ","
                        (Tactic.simpLemma [] [] `true_and_iff)
                        ","
                        (Tactic.simpLemma [] [] `simple_func.coe_const)
                        ","
                        (Tactic.simpLemma [] [] `or_false_iff)
                        ","
                        (Tactic.simpLemma [] [] `lintegral_const)
                        ","
                        (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                        ","
                        (Tactic.simpLemma [] [] `Set.univ_inter)
                        ","
                        (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
                        ","
                        (Tactic.simpLemma [] [] (Term.app `restrict_apply [`MeasurableSet.univ]))
                        ","
                        (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
                        ","
                        (Tactic.simpLemma [] [] `simple_func.const_zero)
                        ","
                        (Tactic.simpLemma [] [] `Function.const_apply)
                        ","
                        (Tactic.simpLemma [] [] `lintegral_indicator)
                        ","
                        (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
                        ","
                        (Tactic.simpLemma [] [] `Ne.def)
                        ","
                        (Tactic.simpLemma [] [] `not_false_iff)
                        ","
                        (Tactic.simpLemma [] [] `simple_func.coe_zero)
                        ","
                        (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                        ","
                        (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                        ","
                        (Tactic.simpLemma [] [] `false_and_iff)]
                       "]")]
                     ["using" `int_f]))]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_<_»
                  (Term.typeAscription
                   "("
                   (num "0")
                   ":"
                   [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                   ")")
                  "<"
                  («term_/_» `ε "/" `c)))]
               ":="
               (Term.app
                (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
                [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")]))))
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `F)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Fs)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `F_closed)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `μF)])
                   [])]
                 "⟩")])]
             [":"
              («term∃_,_»
               "∃"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `F)] ":" (Term.hole "_") ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent (Term.hole "_"))]
                  ":"
                  («term_⊆_» `F "⊆" `s)
                  ")")])
               ","
               («term_∧_»
                (Term.app `IsClosed [`F])
                "∧"
                («term_<_»
                 (Term.app `μ [`s])
                 "<"
                 («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c)))))]
             [":=" [(Term.app `hs.exists_is_closed_lt_add [`μs_lt_top.ne `this.ne'])]])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `Set.indicator [`F (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
               ","
               (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
               ","
               (Term.app
                `F_closed.upper_semicontinuous_indicator
                [(Term.app `zero_le [(Term.hole "_")])])
               ","
               (Term.hole "_")]
              "⟩"))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `simple_func.coe_const)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.const_zero)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_zero)
                 ","
                 (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
                "]"]
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `Set.indicator_le_indicator_of_subset
                [`Fs
                 (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
                 (Term.hole "_")]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.tacticSuffices_
               "suffices"
               (Term.sufficesDecl
                []
                («term_≤_»
                 («term_*_»
                  (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
                  "*"
                  (Term.app `μ [`s]))
                 "≤"
                 («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
                (Term.byTactic'
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
                        [(Tactic.simpLemma [] [] `hs)
                         ","
                         (Tactic.simpLemma [] [] `F_closed.measurable_set)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_const)
                         ","
                         (Tactic.simpLemma [] [] `Function.const_apply)
                         ","
                         (Tactic.simpLemma [] [] `lintegral_const)
                         ","
                         (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                         ","
                         (Tactic.simpLemma [] [] `Set.univ_inter)
                         ","
                         (Tactic.simpLemma [] [] `MeasurableSet.univ)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.const_zero)
                         ","
                         (Tactic.simpLemma [] [] `lintegral_indicator)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_zero)
                         ","
                         (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                         ","
                         (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                         ","
                         (Tactic.simpLemma [] [] `restrict_apply)]
                        "]")]
                      []))])))))
              []
              (calcTactic
               "calc"
               (calcStep
                («term_≤_»
                 («term_*_»
                  (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
                  "*"
                  (Term.app `μ [`s]))
                 "≤"
                 («term_*_» `c "*" («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c))))
                ":="
                (Term.app `Ennreal.mul_le_mul [`le_rfl `μF.le]))
               [(calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Mathlib.Tactic.tacticSimp_rw__
                      "simp_rw"
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
                      [])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         []
                         (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
                       "]")
                      [])
                     []
                     (Std.Tactic.Simpa.simpa
                      "simpa"
                      []
                      []
                      (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))]))))])])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`A []]
               [(Term.typeSpec
                 ":"
                 («term_≠_»
                  («term_+_»
                   (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                    "∫⁻"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                    ", "
                    (Term.app `f₁ [`x])
                    " ∂"
                    `μ)
                   "+"
                   (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                    "∫⁻"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                    ", "
                    (Term.app `f₂ [`x])
                    " ∂"
                    `μ))
                  "≠"
                  (Order.BoundedOrder.«term⊤» "⊤")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.tacticRwa__
                    "rwa"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))]
                     "]")
                    [])]))))))
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                `h₁
                [(Term.proj
                  (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
                  "."
                  (fieldIdx "1"))
                 (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₁_le_g₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁cont)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁int)])
                    [])]
                  "⟩")])
               [])])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                `h₂
                [(Term.proj
                  (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
                  "."
                  (fieldIdx "2"))
                 (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₂_le_g₂)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂cont)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂int)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
               ","
               (Term.app `g₁cont.add [`g₂cont])
               ","
               (Term.hole "_")]
              "⟩"))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `simple_func.coe_add)
               ","
               (Tactic.simpLemma [] [] `Ennreal.coe_add)
               ","
               (Tactic.simpLemma [] [] `Pi.add_apply)]
              "]"]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))
               ","
               (Tactic.rwRule
                []
                (Term.app `lintegral_add_left [`g₁cont.measurable.coe_nnreal_ennreal]))]
              "]")
             [])
            []
            (convert "convert" [] (Term.app `add_le_add [`g₁int `g₂int]) ["using" (num "1")])
            []
            (Tactic.simp "simp" [] [] ["only"] [] [])
            []
            (Mathlib.Tactic.Conv.convLHS
             "conv_lhs"
             []
             []
             "=>"
             (Tactic.Conv.convSeq
              (Tactic.Conv.convSeq1Indented
               [(Tactic.Conv.convRw__
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app `Ennreal.add_halves [`ε]))]
                  "]"))])))
            []
            (Tactic.abel "abel" [] [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`A []]
           [(Term.typeSpec
             ":"
             («term_≠_»
              («term_+_»
               (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                "∫⁻"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                ", "
                (Term.app `f₁ [`x])
                " ∂"
                `μ)
               "+"
               (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                "∫⁻"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
                ", "
                (Term.app `f₂ [`x])
                " ∂"
                `μ))
              "≠"
              (Order.BoundedOrder.«term⊤» "⊤")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))]
                 "]")
                [])]))))))
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            `h₁
            [(Term.proj
              (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
              "."
              (fieldIdx "1"))
             (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₁_le_g₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁cont)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁int)])
                [])]
              "⟩")])
           [])])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            `h₂
            [(Term.proj
              (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
              "."
              (fieldIdx "2"))
             (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₂_le_g₂)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂cont)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂int)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun [`x] [] "=>" («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
           ","
           (Term.app `g₁cont.add [`g₂cont])
           ","
           (Term.hole "_")]
          "⟩"))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `simple_func.coe_add)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_add)
           ","
           (Tactic.simpLemma [] [] `Pi.add_apply)]
          "]"]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))
           ","
           (Tactic.rwRule
            []
            (Term.app `lintegral_add_left [`g₁cont.measurable.coe_nnreal_ennreal]))]
          "]")
         [])
        []
        (convert "convert" [] (Term.app `add_le_add [`g₁int `g₂int]) ["using" (num "1")])
        []
        (Tactic.simp "simp" [] [] ["only"] [] [])
        []
        (Mathlib.Tactic.Conv.convLHS
         "conv_lhs"
         []
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `Ennreal.add_halves [`ε]))]
              "]"))])))
        []
        (Tactic.abel "abel" [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.abel "abel" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convLHS
       "conv_lhs"
       []
       []
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.convRw__
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Ennreal.add_halves [`ε]))]
            "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ennreal.add_halves [`ε])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.add_halves
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `add_le_add [`g₁int `g₂int]) ["using" (num "1")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_le_add [`g₁int `g₂int])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₂int
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g₁int
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_le_add
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
        [(Tactic.rwRule [] (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))
         ","
         (Tactic.rwRule [] (Term.app `lintegral_add_left [`g₁cont.measurable.coe_nnreal_ennreal]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lintegral_add_left [`g₁cont.measurable.coe_nnreal_ennreal])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₁cont.measurable.coe_nnreal_ennreal
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lintegral_add_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₁.measurable.coe_nnreal_ennreal
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lintegral_add_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `simple_func.coe_add)
         ","
         (Tactic.simpLemma [] [] `Ennreal.coe_add)
         ","
         (Tactic.simpLemma [] [] `Pi.add_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.add_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun [`x] [] "=>" («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
         ","
         (Term.app `g₁cont.add [`g₂cont])
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun [`x] [] "=>" («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
        ","
        (Term.app `g₁cont.add [`g₂cont])
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g₁cont.add [`g₂cont])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₂cont
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g₁cont.add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_le_add [(Term.app `f₁_le_g₁ [`x]) (Term.app `f₂_le_g₂ [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f₂_le_g₂ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f₂_le_g₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f₂_le_g₂ [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f₁_le_g₁ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f₁_le_g₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f₁_le_g₁ [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_le_add
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
      (Term.fun
       "fun"
       (Term.basicFun [`x] [] "=>" («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `g₁ [`x]) "+" (Term.app `g₂ [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g₂ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `g₁ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          `h₂
          [(Term.proj
            (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
            "."
            (fieldIdx "2"))
           (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₂_le_g₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂cont)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₂int)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h₂
       [(Term.proj
         (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
         "."
         (fieldIdx "2"))
        (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Ennreal.half_pos [`ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.half_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Ennreal.half_pos [`ε0]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Ennreal.add_ne_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          `h₁
          [(Term.proj
            (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
            "."
            (fieldIdx "1"))
           (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₁_le_g₁)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁cont)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g₁int)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h₁
       [(Term.proj
         (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
         "."
         (fieldIdx "1"))
        (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Ennreal.half_pos [`ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.half_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Ennreal.half_pos [`ε0]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Ennreal.add_ne_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `Ennreal.add_ne_top "." (fieldIdx "1")) [`A])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`A []]
         [(Term.typeSpec
           ":"
           («term_≠_»
            («term_+_»
             (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
              "∫⁻"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
              ", "
              (Term.app `f₁ [`x])
              " ∂"
              `μ)
             "+"
             (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
              "∫⁻"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
              ", "
              (Term.app `f₂ [`x])
              " ∂"
              `μ))
            "≠"
            (Order.BoundedOrder.«term⊤» "⊤")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))]
               "]")
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lintegral_add_left [`f₁.measurable.coe_nnreal_ennreal])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₁.measurable.coe_nnreal_ennreal
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lintegral_add_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       («term_+_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
         ", "
         (Term.app `f₁ [`x])
         " ∂"
         `μ)
        "+"
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
         ", "
         (Term.app `f₂ [`x])
         " ∂"
         `μ))
       "≠"
       (Order.BoundedOrder.«term⊤» "⊤"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
        ", "
        (Term.app `f₁ [`x])
        " ∂"
        `μ)
       "+"
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
        ", "
        (Term.app `f₂ [`x])
        " ∂"
        `μ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
       ", "
       (Term.app `f₂ [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f₂ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
       ", "
       (Term.app `f₁ [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f₁ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
      ", "
      (Term.app `f₁ [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      (Term.paren
       "("
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
        ", "
        (Term.app `f₁ [`x])
        " ∂"
        `μ)
       ")")
      "+"
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `α)]))
       ", "
       (Term.app `f₂ [`x])
       " ∂"
       `μ))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `f
           []
           []
           ":="
           (Term.app
            `simple_func.piecewise
            [`s
             `hs
             (Term.app `simple_func.const [`α `c])
             (Term.app `simple_func.const [`α (num "0")])]))))
        []
        (Classical.«tacticBy_cases_:_» "by_cases" [`hc ":"] («term_=_» `c "=" (num "0")))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
             ","
             (Term.hole "_")
             ","
             `upper_semicontinuous_const
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `hc)
               ","
               (Tactic.simpLemma [] [] `Set.indicator_zero')
               ","
               (Tactic.simpLemma [] [] `Pi.zero_apply)
               ","
               (Tactic.simpLemma [] [] `simple_func.const_zero)
               ","
               (Tactic.simpLemma [] [] `imp_true_iff)
               ","
               (Tactic.simpLemma [] [] `eq_self_iff_true)
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_zero)
               ","
               (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
               ","
               (Tactic.simpLemma [] [] `le_zero_iff)]
              "]"]
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
              [(Tactic.simpLemma [] [] `hc)
               ","
               (Tactic.simpLemma [] [] `Set.indicator_zero')
               ","
               (Tactic.simpLemma [] [] `lintegral_const)
               ","
               (Tactic.simpLemma [] [] `zero_mul)
               ","
               (Tactic.simpLemma [] [] `Pi.zero_apply)
               ","
               (Tactic.simpLemma [] [] `simple_func.const_zero)
               ","
               (Tactic.simpLemma [] [] `zero_add)
               ","
               (Tactic.simpLemma [] [] `zero_le')
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_zero)
               ","
               (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
               ","
               (Tactic.simpLemma [] [] `Ennreal.coe_zero)
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
               ","
               (Tactic.simpLemma [] [] `zero_le)]
              "]"]
             [])])])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`μs_lt_top []]
           [(Term.typeSpec
             ":"
             («term_<_» (Term.app `μ [`s]) "<" (Ennreal.Data.Real.Ennreal.ennreal.top "∞")))]
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
                   [(Tactic.simpLemma [] [] `hs)
                    ","
                    (Tactic.simpLemma [] [] `hc)
                    ","
                    (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
                    ","
                    (Tactic.simpLemma [] [] `true_and_iff)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_const)
                    ","
                    (Tactic.simpLemma [] [] `or_false_iff)
                    ","
                    (Tactic.simpLemma [] [] `lintegral_const)
                    ","
                    (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                    ","
                    (Tactic.simpLemma [] [] `Set.univ_inter)
                    ","
                    (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
                    ","
                    (Tactic.simpLemma [] [] (Term.app `restrict_apply [`MeasurableSet.univ]))
                    ","
                    (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.const_zero)
                    ","
                    (Tactic.simpLemma [] [] `Function.const_apply)
                    ","
                    (Tactic.simpLemma [] [] `lintegral_indicator)
                    ","
                    (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
                    ","
                    (Tactic.simpLemma [] [] `Ne.def)
                    ","
                    (Tactic.simpLemma [] [] `not_false_iff)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_zero)
                    ","
                    (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                    ","
                    (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                    ","
                    (Tactic.simpLemma [] [] `false_and_iff)]
                   "]")]
                 ["using" `int_f]))]))))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_<_»
              (Term.typeAscription
               "("
               (num "0")
               ":"
               [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
               ")")
              "<"
              («term_/_» `ε "/" `c)))]
           ":="
           (Term.app
            (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
            [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")]))))
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `F)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Fs)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `F_closed)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `μF)])
               [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders
            [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `F)] ":" (Term.hole "_") ")")
             (Lean.bracketedExplicitBinders
              "("
              [(Lean.binderIdent (Term.hole "_"))]
              ":"
              («term_⊆_» `F "⊆" `s)
              ")")])
           ","
           («term_∧_»
            (Term.app `IsClosed [`F])
            "∧"
            («term_<_»
             (Term.app `μ [`s])
             "<"
             («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c)))))]
         [":=" [(Term.app `hs.exists_is_closed_lt_add [`μs_lt_top.ne `this.ne'])]])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `Set.indicator [`F (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
           ","
           (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
           ","
           (Term.app
            `F_closed.upper_semicontinuous_indicator
            [(Term.app `zero_le [(Term.hole "_")])])
           ","
           (Term.hole "_")]
          "⟩"))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `simple_func.coe_const)
             ","
             (Tactic.simpLemma [] [] `simple_func.const_zero)
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_zero)
             ","
             (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
            "]"]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `Set.indicator_le_indicator_of_subset
            [`Fs
             (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
             (Term.hole "_")]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            («term_≤_»
             («term_*_»
              (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
              "*"
              (Term.app `μ [`s]))
             "≤"
             («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
            (Term.byTactic'
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
                    [(Tactic.simpLemma [] [] `hs)
                     ","
                     (Tactic.simpLemma [] [] `F_closed.measurable_set)
                     ","
                     (Tactic.simpLemma [] [] `simple_func.coe_const)
                     ","
                     (Tactic.simpLemma [] [] `Function.const_apply)
                     ","
                     (Tactic.simpLemma [] [] `lintegral_const)
                     ","
                     (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                     ","
                     (Tactic.simpLemma [] [] `Set.univ_inter)
                     ","
                     (Tactic.simpLemma [] [] `MeasurableSet.univ)
                     ","
                     (Tactic.simpLemma [] [] `simple_func.const_zero)
                     ","
                     (Tactic.simpLemma [] [] `lintegral_indicator)
                     ","
                     (Tactic.simpLemma [] [] `simple_func.coe_zero)
                     ","
                     (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                     ","
                     (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                     ","
                     (Tactic.simpLemma [] [] `restrict_apply)]
                    "]")]
                  []))])))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             («term_*_»
              (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
              "*"
              (Term.app `μ [`s]))
             "≤"
             («term_*_» `c "*" («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c))))
            ":="
            (Term.app `Ennreal.mul_le_mul [`le_rfl `μF.le]))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.tacticSimp_rw__
                  "simp_rw"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
                   "]")
                  [])
                 []
                 (Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))]))))])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term_≤_»
           («term_*_»
            (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
            "*"
            (Term.app `μ [`s]))
           "≤"
           («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
          (Term.byTactic'
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
                  [(Tactic.simpLemma [] [] `hs)
                   ","
                   (Tactic.simpLemma [] [] `F_closed.measurable_set)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_const)
                   ","
                   (Tactic.simpLemma [] [] `Function.const_apply)
                   ","
                   (Tactic.simpLemma [] [] `lintegral_const)
                   ","
                   (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                   ","
                   (Tactic.simpLemma [] [] `Set.univ_inter)
                   ","
                   (Tactic.simpLemma [] [] `MeasurableSet.univ)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.const_zero)
                   ","
                   (Tactic.simpLemma [] [] `lintegral_indicator)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_zero)
                   ","
                   (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                   ","
                   (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                   ","
                   (Tactic.simpLemma [] [] `restrict_apply)]
                  "]")]
                []))])))))
        []
        (calcTactic
         "calc"
         (calcStep
          («term_≤_»
           («term_*_»
            (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
            "*"
            (Term.app `μ [`s]))
           "≤"
           («term_*_» `c "*" («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c))))
          ":="
          (Term.app `Ennreal.mul_le_mul [`le_rfl `μF.le]))
         [(calcStep
           («term_=_» (Term.hole "_") "=" («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
                [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   []
                   (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
                 "]")
                [])
               []
               (Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))]))))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         («term_*_»
          (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
          "*"
          (Term.app `μ [`s]))
         "≤"
         («term_*_» `c "*" («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c))))
        ":="
        (Term.app `Ennreal.mul_le_mul [`le_rfl `μF.le]))
       [(calcStep
         («term_=_» (Term.hole "_") "=" («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
               "]")
              [])
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
            "]")
           [])
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hc]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
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
          []
          (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ennreal.mul_div_cancel' [(Term.hole "_") `Ennreal.coe_ne_top])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_ne_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.mul_div_cancel'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_add)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» `c "*" (Term.app `μ [`F]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `μ [`F])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `Ennreal.mul_le_mul [`le_rfl `μF.le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μF.le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `le_rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.mul_le_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term_*_»
        (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
        "*"
        (Term.app `μ [`s]))
       "≤"
       («term_*_» `c "*" («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `c "*" («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `μ [`F])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
       "*"
       (Term.app `μ [`s]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `μ [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        («term_≤_»
         («term_*_»
          (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
          "*"
          (Term.app `μ [`s]))
         "≤"
         («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
        (Term.byTactic'
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
                [(Tactic.simpLemma [] [] `hs)
                 ","
                 (Tactic.simpLemma [] [] `F_closed.measurable_set)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_const)
                 ","
                 (Tactic.simpLemma [] [] `Function.const_apply)
                 ","
                 (Tactic.simpLemma [] [] `lintegral_const)
                 ","
                 (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                 ","
                 (Tactic.simpLemma [] [] `Set.univ_inter)
                 ","
                 (Tactic.simpLemma [] [] `MeasurableSet.univ)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.const_zero)
                 ","
                 (Tactic.simpLemma [] [] `lintegral_indicator)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_zero)
                 ","
                 (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                 ","
                 (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                 ","
                 (Tactic.simpLemma [] [] `restrict_apply)]
                "]")]
              []))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
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
          [(Tactic.simpLemma [] [] `hs)
           ","
           (Tactic.simpLemma [] [] `F_closed.measurable_set)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_const)
           ","
           (Tactic.simpLemma [] [] `Function.const_apply)
           ","
           (Tactic.simpLemma [] [] `lintegral_const)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
           ","
           (Tactic.simpLemma [] [] `Set.univ_inter)
           ","
           (Tactic.simpLemma [] [] `MeasurableSet.univ)
           ","
           (Tactic.simpLemma [] [] `simple_func.const_zero)
           ","
           (Tactic.simpLemma [] [] `lintegral_indicator)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_zero)
           ","
           (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
           ","
           (Tactic.simpLemma [] [] `restrict_apply)]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `restrict_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_piecewise
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.piecewise_eq_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lintegral_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.const_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MeasurableSet.univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.univ_inter
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lintegral_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.const_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F_closed.measurable_set
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       («term_*_»
        (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
        "*"
        (Term.app `μ [`s]))
       "≤"
       («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term_*_» `c "*" (Term.app `μ [`F])) "+" `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» `c "*" (Term.app `μ [`F]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `μ [`F])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
       "*"
       (Term.app `μ [`s]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `μ [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription "(" `c ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `simple_func.coe_const)
           ","
           (Tactic.simpLemma [] [] `simple_func.const_zero)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_zero)
           ","
           (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
          "]"]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `Set.indicator_le_indicator_of_subset
          [`Fs
           (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
           (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Set.indicator_le_indicator_of_subset
        [`Fs
         (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Set.indicator_le_indicator_of_subset
       [`Fs
        (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_le [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_le
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `zero_le [(Term.hole "_")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Fs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.indicator_le_indicator_of_subset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `simple_func.coe_const)
         ","
         (Tactic.simpLemma [] [] `simple_func.const_zero)
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_zero)
         ","
         (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_piecewise)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_piecewise
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.piecewise_eq_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.const_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `Set.indicator [`F (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
         ","
         (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
         ","
         (Term.app `F_closed.upper_semicontinuous_indicator [(Term.app `zero_le [(Term.hole "_")])])
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `Set.indicator [`F (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
        ","
        (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
        ","
        (Term.app `F_closed.upper_semicontinuous_indicator [(Term.app `zero_le [(Term.hole "_")])])
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `F_closed.upper_semicontinuous_indicator [(Term.app `zero_le [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_le [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `zero_le [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `F_closed.upper_semicontinuous_indicator
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.indicator [`F (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.indicator
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `F)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Fs)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `F_closed)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `μF)])
             [])]
           "⟩")])]
       [":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `F)] ":" (Term.hole "_") ")")
           (Lean.bracketedExplicitBinders
            "("
            [(Lean.binderIdent (Term.hole "_"))]
            ":"
            («term_⊆_» `F "⊆" `s)
            ")")])
         ","
         («term_∧_»
          (Term.app `IsClosed [`F])
          "∧"
          («term_<_»
           (Term.app `μ [`s])
           "<"
           («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c)))))]
       [":=" [(Term.app `hs.exists_is_closed_lt_add [`μs_lt_top.ne `this.ne'])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hs.exists_is_closed_lt_add [`μs_lt_top.ne `this.ne'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this.ne'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `μs_lt_top.ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hs.exists_is_closed_lt_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `F)] ":" (Term.hole "_") ")")
         (Lean.bracketedExplicitBinders
          "("
          [(Lean.binderIdent (Term.hole "_"))]
          ":"
          («term_⊆_» `F "⊆" `s)
          ")")])
       ","
       («term_∧_»
        (Term.app `IsClosed [`F])
        "∧"
        («term_<_»
         (Term.app `μ [`s])
         "<"
         («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.app `IsClosed [`F])
       "∧"
       («term_<_» (Term.app `μ [`s]) "<" («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.app `μ [`s]) "<" («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `μ [`F]) "+" («term_/_» `ε "/" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `μ [`F])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `μ [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app `IsClosed [`F])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsClosed
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 1023, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⊆_» `F "⊆" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `F
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_<_»
            (Term.typeAscription "(" (num "0") ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
            "<"
            («term_/_» `ε "/" `c)))]
         ":="
         (Term.app
          (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
          [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
       [(Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`ε0 "," `Ennreal.coe_ne_top] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_ne_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Ennreal.div_pos_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.typeAscription "(" (num "0") ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
       "<"
       («term_/_» `ε "/" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (num "0") ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
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
         [`μs_lt_top []]
         [(Term.typeSpec
           ":"
           («term_<_» (Term.app `μ [`s]) "<" (Ennreal.Data.Real.Ennreal.ennreal.top "∞")))]
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
                 [(Tactic.simpLemma [] [] `hs)
                  ","
                  (Tactic.simpLemma [] [] `hc)
                  ","
                  (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
                  ","
                  (Tactic.simpLemma [] [] `true_and_iff)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_const)
                  ","
                  (Tactic.simpLemma [] [] `or_false_iff)
                  ","
                  (Tactic.simpLemma [] [] `lintegral_const)
                  ","
                  (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
                  ","
                  (Tactic.simpLemma [] [] `Set.univ_inter)
                  ","
                  (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `restrict_apply [`MeasurableSet.univ]))
                  ","
                  (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.const_zero)
                  ","
                  (Tactic.simpLemma [] [] `Function.const_apply)
                  ","
                  (Tactic.simpLemma [] [] `lintegral_indicator)
                  ","
                  (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
                  ","
                  (Tactic.simpLemma [] [] `Ne.def)
                  ","
                  (Tactic.simpLemma [] [] `not_false_iff)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_zero)
                  ","
                  (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
                  ","
                  (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
                  ","
                  (Tactic.simpLemma [] [] `false_and_iff)]
                 "]")]
               ["using" `int_f]))]))))))
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
              [(Tactic.simpLemma [] [] `hs)
               ","
               (Tactic.simpLemma [] [] `hc)
               ","
               (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
               ","
               (Tactic.simpLemma [] [] `true_and_iff)
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_const)
               ","
               (Tactic.simpLemma [] [] `or_false_iff)
               ","
               (Tactic.simpLemma [] [] `lintegral_const)
               ","
               (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
               ","
               (Tactic.simpLemma [] [] `Set.univ_inter)
               ","
               (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
               ","
               (Tactic.simpLemma [] [] (Term.app `restrict_apply [`MeasurableSet.univ]))
               ","
               (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
               ","
               (Tactic.simpLemma [] [] `simple_func.const_zero)
               ","
               (Tactic.simpLemma [] [] `Function.const_apply)
               ","
               (Tactic.simpLemma [] [] `lintegral_indicator)
               ","
               (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
               ","
               (Tactic.simpLemma [] [] `Ne.def)
               ","
               (Tactic.simpLemma [] [] `not_false_iff)
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_zero)
               ","
               (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
               ","
               (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
               ","
               (Tactic.simpLemma [] [] `false_and_iff)]
              "]")]
            ["using" `int_f]))])))
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
          [(Tactic.simpLemma [] [] `hs)
           ","
           (Tactic.simpLemma [] [] `hc)
           ","
           (Tactic.simpLemma [] [] `lt_top_iff_ne_top)
           ","
           (Tactic.simpLemma [] [] `true_and_iff)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_const)
           ","
           (Tactic.simpLemma [] [] `or_false_iff)
           ","
           (Tactic.simpLemma [] [] `lintegral_const)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_indicator)
           ","
           (Tactic.simpLemma [] [] `Set.univ_inter)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_ne_top)
           ","
           (Tactic.simpLemma [] [] (Term.app `restrict_apply [`MeasurableSet.univ]))
           ","
           (Tactic.simpLemma [] [] `WithTop.mul_eq_top_iff)
           ","
           (Tactic.simpLemma [] [] `simple_func.const_zero)
           ","
           (Tactic.simpLemma [] [] `Function.const_apply)
           ","
           (Tactic.simpLemma [] [] `lintegral_indicator)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_eq_zero)
           ","
           (Tactic.simpLemma [] [] `Ne.def)
           ","
           (Tactic.simpLemma [] [] `not_false_iff)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_zero)
           ","
           (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
           ","
           (Tactic.simpLemma [] [] `false_and_iff)]
          "]")]
        ["using" `int_f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `int_f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `false_and_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_piecewise
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.piecewise_eq_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
      `Ennreal.coe_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lintegral_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.const_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.const_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WithTop.mul_eq_top_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `restrict_apply [`MeasurableSet.univ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MeasurableSet.univ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `restrict_apply
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_ne_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.univ_inter
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lintegral_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `or_false_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true_and_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lt_top_iff_ne_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.app `μ [`s]) "<" (Ennreal.Data.Real.Ennreal.ennreal.top "∞"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal.top "∞")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `μ [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
           ","
           (Term.hole "_")
           ","
           `upper_semicontinuous_const
           ","
           (Term.hole "_")]
          "⟩"))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `hc)
             ","
             (Tactic.simpLemma [] [] `Set.indicator_zero')
             ","
             (Tactic.simpLemma [] [] `Pi.zero_apply)
             ","
             (Tactic.simpLemma [] [] `simple_func.const_zero)
             ","
             (Tactic.simpLemma [] [] `imp_true_iff)
             ","
             (Tactic.simpLemma [] [] `eq_self_iff_true)
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_zero)
             ","
             (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
             ","
             (Tactic.simpLemma [] [] `le_zero_iff)]
            "]"]
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
            [(Tactic.simpLemma [] [] `hc)
             ","
             (Tactic.simpLemma [] [] `Set.indicator_zero')
             ","
             (Tactic.simpLemma [] [] `lintegral_const)
             ","
             (Tactic.simpLemma [] [] `zero_mul)
             ","
             (Tactic.simpLemma [] [] `Pi.zero_apply)
             ","
             (Tactic.simpLemma [] [] `simple_func.const_zero)
             ","
             (Tactic.simpLemma [] [] `zero_add)
             ","
             (Tactic.simpLemma [] [] `zero_le')
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_zero)
             ","
             (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
             ","
             (Tactic.simpLemma [] [] `Ennreal.coe_zero)
             ","
             (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
             ","
             (Tactic.simpLemma [] [] `zero_le)]
            "]"]
           [])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `hc)
           ","
           (Tactic.simpLemma [] [] `Set.indicator_zero')
           ","
           (Tactic.simpLemma [] [] `lintegral_const)
           ","
           (Tactic.simpLemma [] [] `zero_mul)
           ","
           (Tactic.simpLemma [] [] `Pi.zero_apply)
           ","
           (Tactic.simpLemma [] [] `simple_func.const_zero)
           ","
           (Tactic.simpLemma [] [] `zero_add)
           ","
           (Tactic.simpLemma [] [] `zero_le')
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_zero)
           ","
           (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_zero)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
           ","
           (Tactic.simpLemma [] [] `zero_le)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `hc)
         ","
         (Tactic.simpLemma [] [] `Set.indicator_zero')
         ","
         (Tactic.simpLemma [] [] `lintegral_const)
         ","
         (Tactic.simpLemma [] [] `zero_mul)
         ","
         (Tactic.simpLemma [] [] `Pi.zero_apply)
         ","
         (Tactic.simpLemma [] [] `simple_func.const_zero)
         ","
         (Tactic.simpLemma [] [] `zero_add)
         ","
         (Tactic.simpLemma [] [] `zero_le')
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_zero)
         ","
         (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
         ","
         (Tactic.simpLemma [] [] `Ennreal.coe_zero)
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
         ","
         (Tactic.simpLemma [] [] `zero_le)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_piecewise
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.piecewise_eq_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_le'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.const_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.zero_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lintegral_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.indicator_zero'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `hc)
           ","
           (Tactic.simpLemma [] [] `Set.indicator_zero')
           ","
           (Tactic.simpLemma [] [] `Pi.zero_apply)
           ","
           (Tactic.simpLemma [] [] `simple_func.const_zero)
           ","
           (Tactic.simpLemma [] [] `imp_true_iff)
           ","
           (Tactic.simpLemma [] [] `eq_self_iff_true)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_zero)
           ","
           (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
           ","
           (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
           ","
           (Tactic.simpLemma [] [] `le_zero_iff)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `hc)
         ","
         (Tactic.simpLemma [] [] `Set.indicator_zero')
         ","
         (Tactic.simpLemma [] [] `Pi.zero_apply)
         ","
         (Tactic.simpLemma [] [] `simple_func.const_zero)
         ","
         (Tactic.simpLemma [] [] `imp_true_iff)
         ","
         (Tactic.simpLemma [] [] `eq_self_iff_true)
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_zero)
         ","
         (Tactic.simpLemma [] [] `Set.piecewise_eq_indicator)
         ","
         (Tactic.simpLemma [] [] `simple_func.coe_piecewise)
         ","
         (Tactic.simpLemma [] [] `le_zero_iff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_zero_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_piecewise
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.piecewise_eq_indicator
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_self_iff_true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `imp_true_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.const_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.zero_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.indicator_zero'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
         ","
         (Term.hole "_")
         ","
         `upper_semicontinuous_const
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
        ","
        (Term.hole "_")
        ","
        `upper_semicontinuous_const
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `upper_semicontinuous_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`hc ":"] («term_=_» `c "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `c "=" (num "0"))
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
         `f
         []
         []
         ":="
         (Term.app
          `simple_func.piecewise
          [`s
           `hs
           (Term.app `simple_func.const [`α `c])
           (Term.app `simple_func.const [`α (num "0")])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `simple_func.piecewise
       [`s `hs (Term.app `simple_func.const [`α `c]) (Term.app `simple_func.const [`α (num "0")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `simple_func.const [`α (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simple_func.const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `simple_func.const [`α (num "0")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `simple_func.const [`α `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simple_func.const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `simple_func.const [`α `c])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simple_func.piecewise
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `f)]
       ["using" `MeasureTheory.SimpleFunc.induction]
       ["with"
        [(Lean.binderIdent `c)
         (Lean.binderIdent `s)
         (Lean.binderIdent `hs)
         (Lean.binderIdent `f₁)
         (Lean.binderIdent `f₂)
         (Lean.binderIdent `H)
         (Lean.binderIdent `h₁)
         (Lean.binderIdent `h₂)]]
       ["generalizing" [`ε]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `g)]
         [":" (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
       ","
       («term_∧_»
        (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `f [`x])))
        "∧"
        («term_∧_»
         (Term.app `UpperSemicontinuous [`g])
         "∧"
         («term_≤_»
          (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
           "∫⁻"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           ", "
           (Term.app `f [`x])
           " ∂"
           `μ)
          "≤"
          («term_+_»
           (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
            "∫⁻"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
            ", "
            (Term.app `g [`x])
            " ∂"
            `μ)
           "+"
           `ε)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `f [`x])))
       "∧"
       («term_∧_»
        (Term.app `UpperSemicontinuous [`g])
        "∧"
        («term_≤_»
         (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
          "∫⁻"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app `f [`x])
          " ∂"
          `μ)
         "≤"
         («term_+_»
          (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
           "∫⁻"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           ", "
           (Term.app `g [`x])
           " ∂"
           `μ)
          "+"
          `ε))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.app `UpperSemicontinuous [`g])
       "∧"
       («term_≤_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `f [`x])
         " ∂"
         `μ)
        "≤"
        («term_+_»
         (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
          "∫⁻"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app `g [`x])
          " ∂"
          `μ)
         "+"
         `ε)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `f [`x])
        " ∂"
        `μ)
       "≤"
       («term_+_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `g [`x])
         " ∂"
         `μ)
        "+"
        `ε))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `g [`x])
        " ∂"
        `μ)
       "+"
       `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `g [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `g [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `f [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `f [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app `UpperSemicontinuous [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UpperSemicontinuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 1023, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `f [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.app `g [`x]) "≤" (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 0, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `f [`x])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `ε "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `f [`x])
        " ∂"
        `μ)
       "≠"
       (Ennreal.Data.Real.Ennreal.ennreal.top "∞"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal.top "∞")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `f [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `f [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»
       `α
       " →ₛ "
       (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»', expected 'MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.term_→ₛ_._@.MeasureTheory.Integral.VitaliCaratheodory._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given a simple function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
    function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
    `lintegral`.
    Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
  theorem
    SimpleFunc.exists_upper_semicontinuous_le_lintegral_le
    ( f : α →ₛ ℝ≥0 ) ( int_f : ∫⁻ x , f x ∂ μ ≠ ∞ ) { ε : ℝ≥0∞ } ( ε0 : ε ≠ 0 )
      :
        ∃
          g : α → ℝ≥0
          ,
          ∀ x , g x ≤ f x ∧ UpperSemicontinuous g ∧ ∫⁻ x , f x ∂ μ ≤ ∫⁻ x , g x ∂ μ + ε
    :=
      by
        induction'
            f
            using MeasureTheory.SimpleFunc.induction
            with c s hs f₁ f₂ H h₁ h₂
            generalizing ε
          ·
            let f := simple_func.piecewise s hs simple_func.const α c simple_func.const α 0
              by_cases hc : c = 0
              ·
                refine' ⟨ fun x => 0 , _ , upper_semicontinuous_const , _ ⟩
                  ·
                    simp
                      only
                      [
                        hc
                          ,
                          Set.indicator_zero'
                          ,
                          Pi.zero_apply
                          ,
                          simple_func.const_zero
                          ,
                          imp_true_iff
                          ,
                          eq_self_iff_true
                          ,
                          simple_func.coe_zero
                          ,
                          Set.piecewise_eq_indicator
                          ,
                          simple_func.coe_piecewise
                          ,
                          le_zero_iff
                        ]
                  ·
                    simp
                      only
                      [
                        hc
                          ,
                          Set.indicator_zero'
                          ,
                          lintegral_const
                          ,
                          zero_mul
                          ,
                          Pi.zero_apply
                          ,
                          simple_func.const_zero
                          ,
                          zero_add
                          ,
                          zero_le'
                          ,
                          simple_func.coe_zero
                          ,
                          Set.piecewise_eq_indicator
                          ,
                          Ennreal.coe_zero
                          ,
                          simple_func.coe_piecewise
                          ,
                          zero_le
                        ]
              have
                μs_lt_top
                  : μ s < ∞
                  :=
                  by
                    simpa
                      only
                        [
                          hs
                            ,
                            hc
                            ,
                            lt_top_iff_ne_top
                            ,
                            true_and_iff
                            ,
                            simple_func.coe_const
                            ,
                            or_false_iff
                            ,
                            lintegral_const
                            ,
                            Ennreal.coe_indicator
                            ,
                            Set.univ_inter
                            ,
                            Ennreal.coe_ne_top
                            ,
                            restrict_apply MeasurableSet.univ
                            ,
                            WithTop.mul_eq_top_iff
                            ,
                            simple_func.const_zero
                            ,
                            Function.const_apply
                            ,
                            lintegral_indicator
                            ,
                            Ennreal.coe_eq_zero
                            ,
                            Ne.def
                            ,
                            not_false_iff
                            ,
                            simple_func.coe_zero
                            ,
                            Set.piecewise_eq_indicator
                            ,
                            simple_func.coe_piecewise
                            ,
                            false_and_iff
                          ]
                        using int_f
              have : ( 0 : ℝ≥0∞ ) < ε / c := Ennreal.div_pos_iff . 2 ⟨ ε0 , Ennreal.coe_ne_top ⟩
              obtain
                ⟨ F , Fs , F_closed , μF ⟩
                : ∃ ( F : _ ) ( _ : F ⊆ s ) , IsClosed F ∧ μ s < μ F + ε / c
                := hs.exists_is_closed_lt_add μs_lt_top.ne this.ne'
              refine'
                ⟨
                  Set.indicator F fun x => c
                    ,
                    fun x => _
                    ,
                    F_closed.upper_semicontinuous_indicator zero_le _
                    ,
                    _
                  ⟩
              ·
                simp
                    only
                    [
                      simple_func.coe_const
                        ,
                        simple_func.const_zero
                        ,
                        simple_func.coe_zero
                        ,
                        Set.piecewise_eq_indicator
                        ,
                        simple_func.coe_piecewise
                      ]
                  exact Set.indicator_le_indicator_of_subset Fs fun x => zero_le _ _
              ·
                suffices
                    ( c : ℝ≥0∞ ) * μ s ≤ c * μ F + ε
                      by
                        simpa
                          only
                            [
                              hs
                                ,
                                F_closed.measurable_set
                                ,
                                simple_func.coe_const
                                ,
                                Function.const_apply
                                ,
                                lintegral_const
                                ,
                                Ennreal.coe_indicator
                                ,
                                Set.univ_inter
                                ,
                                MeasurableSet.univ
                                ,
                                simple_func.const_zero
                                ,
                                lintegral_indicator
                                ,
                                simple_func.coe_zero
                                ,
                                Set.piecewise_eq_indicator
                                ,
                                simple_func.coe_piecewise
                                ,
                                restrict_apply
                              ]
                  calc
                    ( c : ℝ≥0∞ ) * μ s ≤ c * μ F + ε / c := Ennreal.mul_le_mul le_rfl μF.le
                    _ = c * μ F + ε
                      :=
                      by
                        simp_rw [ mul_add ]
                          rw [ Ennreal.mul_div_cancel' _ Ennreal.coe_ne_top ]
                          simpa using hc
          ·
            have
                A
                  : ∫⁻ x : α , f₁ x ∂ μ + ∫⁻ x : α , f₂ x ∂ μ ≠ ⊤
                  :=
                  by rwa [ ← lintegral_add_left f₁.measurable.coe_nnreal_ennreal ]
              rcases
                h₁ Ennreal.add_ne_top . 1 A . 1 Ennreal.half_pos ε0 . ne'
                with ⟨ g₁ , f₁_le_g₁ , g₁cont , g₁int ⟩
              rcases
                h₂ Ennreal.add_ne_top . 1 A . 2 Ennreal.half_pos ε0 . ne'
                with ⟨ g₂ , f₂_le_g₂ , g₂cont , g₂int ⟩
              refine'
                ⟨
                  fun x => g₁ x + g₂ x
                    ,
                    fun x => add_le_add f₁_le_g₁ x f₂_le_g₂ x
                    ,
                    g₁cont.add g₂cont
                    ,
                    _
                  ⟩
              simp only [ simple_func.coe_add , Ennreal.coe_add , Pi.add_apply ]
              rw
                [
                  lintegral_add_left f₁.measurable.coe_nnreal_ennreal
                    ,
                    lintegral_add_left g₁cont.measurable.coe_nnreal_ennreal
                  ]
              convert add_le_add g₁int g₂int using 1
              simp only
              conv_lhs => rw [ ← Ennreal.add_halves ε ]
              abel
#align
  measure_theory.simple_func.exists_upper_semicontinuous_le_lintegral_le MeasureTheory.SimpleFunc.exists_upper_semicontinuous_le_lintegral_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous\nfunction `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of\n`lintegral`.\nAuxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_upper_semicontinuous_le_lintegral_le [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`int_f]
         [":"
          («term_≠_»
           (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
            "∫⁻"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
            ", "
            (Term.app `f [`x])
            " ∂"
            `μ)
           "≠"
           (Ennreal.Data.Real.Ennreal.ennreal.top "∞"))]
         []
         ")")
        (Term.implicitBinder "{" [`ε] [":" (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] "}")
        (Term.explicitBinder "(" [`ε0] [":" («term_≠_» `ε "≠" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `g)]
           [":" (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
         ","
         («term_∧_»
          (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `f [`x])))
          "∧"
          («term_∧_»
           (Term.app `UpperSemicontinuous [`g])
           "∧"
           («term_≤_»
            (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
             "∫⁻"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             ", "
             (Term.app `f [`x])
             " ∂"
             `μ)
            "≤"
            («term_+_»
             (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
              "∫⁻"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
              ", "
              (Term.app `g [`x])
              " ∂"
              `μ)
             "+"
             `ε)))))))
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
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs_le_f)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `int_fs)])
                  [])]
                "⟩")])]
            [":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders
                [(Lean.binderIdent `fs)]
                [":"
                 (MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»
                  `α
                  " →ₛ "
                  (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
              ","
              («term_∧_»
               (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `fs [`x]) "≤" (Term.app `f [`x])))
               "∧"
               («term_≤_»
                (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                 "∫⁻"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 ", "
                 (Term.app `f [`x])
                 " ∂"
                 `μ)
                "≤"
                («term_+_»
                 (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                  "∫⁻"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                  ", "
                  (Term.app `fs [`x])
                  " ∂"
                  `μ)
                 "+"
                 («term_/_» `ε "/" (num "2"))))))]
            [":="
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     []
                     ":="
                     (Term.app
                      `Ennreal.lt_add_right
                      [`int_f (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))))
                  []
                  (Mathlib.Tactic.Conv.convRHS
                   "conv_rhs"
                   ["at" `this]
                   []
                   "=>"
                   (Tactic.Conv.convSeq
                    (Tactic.Conv.convSeq1Indented
                     [(Tactic.Conv.convRw__
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule
                          []
                          (Term.app
                           `lintegral_eq_nnreal
                           [(Term.fun
                             "fun"
                             (Term.basicFun
                              [`x]
                              []
                              "=>"
                              (Term.typeAscription
                               "("
                               (Term.app `f [`x])
                               ":"
                               [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                               ")")))
                            `μ]))]
                        "]"))])))
                  []
                  (Std.Tactic.seq_focus
                   (Tactic.tacticErw__
                    "erw"
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ennreal.bsupr_add)] "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                   "<;>"
                   "["
                   [(Tactic.skip "skip")
                    ","
                    (Tactic.exact
                     "exact"
                     (Term.anonymousCtor
                      "⟨"
                      [(num "0")
                       ","
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`x]
                         []
                         "=>"
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))]
                      "⟩"))]
                   "]")
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `lt_supᵢ_iff)] "]"]
                   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget [] `this)]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `fs_le_f)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `int_fs)])
                          [])]
                        "⟩")])
                     [])])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.anonymousCtor
                    "⟨"
                    [`fs
                     ","
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`x]
                       []
                       "=>"
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
                               [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)]
                               "]")]
                             ["using" (Term.app `fs_le_f [`x])]))])))))
                     ","
                     (Term.hole "_")]
                    "⟩"))
                  []
                  (convert "convert" [] `int_fs.le [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      `simple_func.lintegral_eq_lintegral)]
                    "]")
                   [])
                  []
                  (Tactic.tacticRfl "rfl")])))]])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`int_fs_lt_top []]
              [(Term.typeSpec
                ":"
                («term_≠_»
                 (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                  "∫⁻"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                  ", "
                  (Term.app `fs [`x])
                  " ∂"
                  `μ)
                 "≠"
                 (Ennreal.Data.Real.Ennreal.ennreal.top "∞")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.apply
                   "apply"
                   (Term.app
                    `ne_top_of_le_ne_top
                    [`int_f
                     (Term.app
                      `lintegral_mono
                      [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])]))
                  []
                  (Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    ["only"]
                    [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
                    ["using" (Term.app `fs_le_f [`x])]))]))))))
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g_le_fs)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `gcont)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `gint)])
                  [])]
                "⟩")])]
            [":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders
                [(Lean.binderIdent `g)]
                [":" (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
              ","
              («term_∧_»
               (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `fs [`x])))
               "∧"
               («term_∧_»
                (Term.app `UpperSemicontinuous [`g])
                "∧"
                («term_≤_»
                 (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                  "∫⁻"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                  ", "
                  (Term.app `fs [`x])
                  " ∂"
                  `μ)
                 "≤"
                 («term_+_»
                  (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                   "∫⁻"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                   ", "
                   (Term.app `g [`x])
                   " ∂"
                   `μ)
                  "+"
                  («term_/_» `ε "/" (num "2")))))))]
            [":="
             [(Term.app
               `fs.exists_upper_semicontinuous_le_lintegral_le
               [`int_fs_lt_top (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')])]])
           []
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [`g
              ","
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Term.app
                 (Term.proj (Term.app `g_le_fs [`x]) "." `trans)
                 [(Term.app `fs_le_f [`x])])))
              ","
              `gcont
              ","
              (Term.hole "_")]
             "⟩"))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_≤_»
              (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
               "∫⁻"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
               ", "
               (Term.app `f [`x])
               " ∂"
               `μ)
              "≤"
              («term_+_»
               (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                "∫⁻"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                ", "
                (Term.app `fs [`x])
                " ∂"
                `μ)
               "+"
               («term_/_» `ε "/" (num "2"))))
             ":="
             `int_fs)
            [(calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_+_»
                («term_+_»
                 (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                  "∫⁻"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                  ", "
                  (Term.app `g [`x])
                  " ∂"
                  `μ)
                 "+"
                 («term_/_» `ε "/" (num "2")))
                "+"
                («term_/_» `ε "/" (num "2"))))
              ":="
              (Term.app `add_le_add [`gint `le_rfl]))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_+_»
                (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                 "∫⁻"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 ", "
                 (Term.app `g [`x])
                 " ∂"
                 `μ)
                "+"
                `ε))
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
                    [(Tactic.rwRule [] `add_assoc) "," (Tactic.rwRule [] `Ennreal.add_halves)]
                    "]")
                   [])]))))])])))
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
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs_le_f)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `int_fs)])
                 [])]
               "⟩")])]
           [":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `fs)]
               [":"
                (MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»
                 `α
                 " →ₛ "
                 (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
             ","
             («term_∧_»
              (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `fs [`x]) "≤" (Term.app `f [`x])))
              "∧"
              («term_≤_»
               (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                "∫⁻"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                ", "
                (Term.app `f [`x])
                " ∂"
                `μ)
               "≤"
               («term_+_»
                (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                 "∫⁻"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 ", "
                 (Term.app `fs [`x])
                 " ∂"
                 `μ)
                "+"
                («term_/_» `ε "/" (num "2"))))))]
           [":="
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.app
                     `Ennreal.lt_add_right
                     [`int_f (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))))
                 []
                 (Mathlib.Tactic.Conv.convRHS
                  "conv_rhs"
                  ["at" `this]
                  []
                  "=>"
                  (Tactic.Conv.convSeq
                   (Tactic.Conv.convSeq1Indented
                    [(Tactic.Conv.convRw__
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         []
                         (Term.app
                          `lintegral_eq_nnreal
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [`x]
                             []
                             "=>"
                             (Term.typeAscription
                              "("
                              (Term.app `f [`x])
                              ":"
                              [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                              ")")))
                           `μ]))]
                       "]"))])))
                 []
                 (Std.Tactic.seq_focus
                  (Tactic.tacticErw__
                   "erw"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ennreal.bsupr_add)] "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                  "<;>"
                  "["
                  [(Tactic.skip "skip")
                   ","
                   (Tactic.exact
                    "exact"
                    (Term.anonymousCtor
                     "⟨"
                     [(num "0")
                      ","
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [`x]
                        []
                        "=>"
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))]
                     "⟩"))]
                  "]")
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `lt_supᵢ_iff)] "]"]
                  [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget [] `this)]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `fs_le_f)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `int_fs)])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.anonymousCtor
                   "⟨"
                   [`fs
                    ","
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`x]
                      []
                      "=>"
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
                              [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)]
                              "]")]
                            ["using" (Term.app `fs_le_f [`x])]))])))))
                    ","
                    (Term.hole "_")]
                   "⟩"))
                 []
                 (convert "convert" [] `int_fs.le [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     `simple_func.lintegral_eq_lintegral)]
                   "]")
                  [])
                 []
                 (Tactic.tacticRfl "rfl")])))]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`int_fs_lt_top []]
             [(Term.typeSpec
               ":"
               («term_≠_»
                (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                 "∫⁻"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 ", "
                 (Term.app `fs [`x])
                 " ∂"
                 `μ)
                "≠"
                (Ennreal.Data.Real.Ennreal.ennreal.top "∞")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.apply
                  "apply"
                  (Term.app
                   `ne_top_of_le_ne_top
                   [`int_f
                    (Term.app
                     `lintegral_mono
                     [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])]))
                 []
                 (Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   ["only"]
                   [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
                   ["using" (Term.app `fs_le_f [`x])]))]))))))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g_le_fs)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `gcont)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `gint)])
                 [])]
               "⟩")])]
           [":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `g)]
               [":" (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
             ","
             («term_∧_»
              (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `fs [`x])))
              "∧"
              («term_∧_»
               (Term.app `UpperSemicontinuous [`g])
               "∧"
               («term_≤_»
                (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                 "∫⁻"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 ", "
                 (Term.app `fs [`x])
                 " ∂"
                 `μ)
                "≤"
                («term_+_»
                 (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                  "∫⁻"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                  ", "
                  (Term.app `g [`x])
                  " ∂"
                  `μ)
                 "+"
                 («term_/_» `ε "/" (num "2")))))))]
           [":="
            [(Term.app
              `fs.exists_upper_semicontinuous_le_lintegral_le
              [`int_fs_lt_top (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')])]])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [`g
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Term.app
                (Term.proj (Term.app `g_le_fs [`x]) "." `trans)
                [(Term.app `fs_le_f [`x])])))
             ","
             `gcont
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
              "∫⁻"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
              ", "
              (Term.app `f [`x])
              " ∂"
              `μ)
             "≤"
             («term_+_»
              (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
               "∫⁻"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
               ", "
               (Term.app `fs [`x])
               " ∂"
               `μ)
              "+"
              («term_/_» `ε "/" (num "2"))))
            ":="
            `int_fs)
           [(calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_+_»
               («term_+_»
                (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                 "∫⁻"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 ", "
                 (Term.app `g [`x])
                 " ∂"
                 `μ)
                "+"
                («term_/_» `ε "/" (num "2")))
               "+"
               («term_/_» `ε "/" (num "2"))))
             ":="
             (Term.app `add_le_add [`gint `le_rfl]))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
                "∫⁻"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                ", "
                (Term.app `g [`x])
                " ∂"
                `μ)
               "+"
               `ε))
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
                   [(Tactic.rwRule [] `add_assoc) "," (Tactic.rwRule [] `Ennreal.add_halves)]
                   "]")
                  [])]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
          "∫⁻"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app `f [`x])
          " ∂"
          `μ)
         "≤"
         («term_+_»
          (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
           "∫⁻"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           ", "
           (Term.app `fs [`x])
           " ∂"
           `μ)
          "+"
          («term_/_» `ε "/" (num "2"))))
        ":="
        `int_fs)
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_»
           («term_+_»
            (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
             "∫⁻"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             ", "
             (Term.app `g [`x])
             " ∂"
             `μ)
            "+"
            («term_/_» `ε "/" (num "2")))
           "+"
           («term_/_» `ε "/" (num "2"))))
         ":="
         (Term.app `add_le_add [`gint `le_rfl]))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
            "∫⁻"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
            ", "
            (Term.app `g [`x])
            " ∂"
            `μ)
           "+"
           `ε))
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
               [(Tactic.rwRule [] `add_assoc) "," (Tactic.rwRule [] `Ennreal.add_halves)]
               "]")
              [])]))))])
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
            [(Tactic.rwRule [] `add_assoc) "," (Tactic.rwRule [] `Ennreal.add_halves)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `add_assoc) "," (Tactic.rwRule [] `Ennreal.add_halves)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.add_halves
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_+_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `g [`x])
         " ∂"
         `μ)
        "+"
        `ε))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `g [`x])
        " ∂"
        `μ)
       "+"
       `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `g [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `g [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `add_le_add [`gint `le_rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `gint
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_le_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_+_»
        («term_+_»
         (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
          "∫⁻"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app `g [`x])
          " ∂"
          `μ)
         "+"
         («term_/_» `ε "/" (num "2")))
        "+"
        («term_/_» `ε "/" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_+_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `g [`x])
         " ∂"
         `μ)
        "+"
        («term_/_» `ε "/" (num "2")))
       "+"
       («term_/_» `ε "/" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `g [`x])
        " ∂"
        `μ)
       "+"
       («term_/_» `ε "/" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `g [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `g [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      `int_fs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `f [`x])
        " ∂"
        `μ)
       "≤"
       («term_+_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `fs [`x])
         " ∂"
         `μ)
        "+"
        («term_/_» `ε "/" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `fs [`x])
        " ∂"
        `μ)
       "+"
       («term_/_» `ε "/" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `fs [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fs [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `fs [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `f [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `f [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [`g
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app (Term.proj (Term.app `g_le_fs [`x]) "." `trans) [(Term.app `fs_le_f [`x])])))
         ","
         `gcont
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`g
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app (Term.proj (Term.app `g_le_fs [`x]) "." `trans) [(Term.app `fs_le_f [`x])])))
        ","
        `gcont
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gcont
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app (Term.proj (Term.app `g_le_fs [`x]) "." `trans) [(Term.app `fs_le_f [`x])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `g_le_fs [`x]) "." `trans) [(Term.app `fs_le_f [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fs_le_f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs_le_f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `fs_le_f [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `g_le_fs [`x]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `g_le_fs [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g_le_fs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `g_le_fs [`x]) ")")
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
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g_le_fs)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `gcont)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `gint)])
             [])]
           "⟩")])]
       [":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `g)]
           [":" (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
         ","
         («term_∧_»
          (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `fs [`x])))
          "∧"
          («term_∧_»
           (Term.app `UpperSemicontinuous [`g])
           "∧"
           («term_≤_»
            (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
             "∫⁻"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             ", "
             (Term.app `fs [`x])
             " ∂"
             `μ)
            "≤"
            («term_+_»
             (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
              "∫⁻"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
              ", "
              (Term.app `g [`x])
              " ∂"
              `μ)
             "+"
             («term_/_» `ε "/" (num "2")))))))]
       [":="
        [(Term.app
          `fs.exists_upper_semicontinuous_le_lintegral_le
          [`int_fs_lt_top (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `fs.exists_upper_semicontinuous_le_lintegral_le
       [`int_fs_lt_top (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Ennreal.half_pos [`ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.half_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Ennreal.half_pos [`ε0]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `int_fs_lt_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs.exists_upper_semicontinuous_le_lintegral_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `g)]
         [":" (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
       ","
       («term_∧_»
        (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `fs [`x])))
        "∧"
        («term_∧_»
         (Term.app `UpperSemicontinuous [`g])
         "∧"
         («term_≤_»
          (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
           "∫⁻"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           ", "
           (Term.app `fs [`x])
           " ∂"
           `μ)
          "≤"
          («term_+_»
           (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
            "∫⁻"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
            ", "
            (Term.app `g [`x])
            " ∂"
            `μ)
           "+"
           («term_/_» `ε "/" (num "2")))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `fs [`x])))
       "∧"
       («term_∧_»
        (Term.app `UpperSemicontinuous [`g])
        "∧"
        («term_≤_»
         (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
          "∫⁻"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app `fs [`x])
          " ∂"
          `μ)
         "≤"
         («term_+_»
          (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
           "∫⁻"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           ", "
           (Term.app `g [`x])
           " ∂"
           `μ)
          "+"
          («term_/_» `ε "/" (num "2"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.app `UpperSemicontinuous [`g])
       "∧"
       («term_≤_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `fs [`x])
         " ∂"
         `μ)
        "≤"
        («term_+_»
         (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
          "∫⁻"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app `g [`x])
          " ∂"
          `μ)
         "+"
         («term_/_» `ε "/" (num "2")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `fs [`x])
        " ∂"
        `μ)
       "≤"
       («term_+_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `g [`x])
         " ∂"
         `μ)
        "+"
        («term_/_» `ε "/" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `g [`x])
        " ∂"
        `μ)
       "+"
       («term_/_» `ε "/" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `g [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `g [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `fs [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fs [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `fs [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app `UpperSemicontinuous [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UpperSemicontinuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 1023, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `fs [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.app `g [`x]) "≤" (Term.app `fs [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fs [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 0, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `g [`x]) "≤" (Term.app `fs [`x])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `α "→" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`int_fs_lt_top []]
         [(Term.typeSpec
           ":"
           («term_≠_»
            (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
             "∫⁻"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             ", "
             (Term.app `fs [`x])
             " ∂"
             `μ)
            "≠"
            (Ennreal.Data.Real.Ennreal.ennreal.top "∞")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.apply
              "apply"
              (Term.app
               `ne_top_of_le_ne_top
               [`int_f
                (Term.app
                 `lintegral_mono
                 [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])]))
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               ["only"]
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
               ["using" (Term.app `fs_le_f [`x])]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply
           "apply"
           (Term.app
            `ne_top_of_le_ne_top
            [`int_f
             (Term.app
              `lintegral_mono
              [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])]))
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
            ["using" (Term.app `fs_le_f [`x])]))])))
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
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
        ["using" (Term.app `fs_le_f [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fs_le_f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs_le_f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `ne_top_of_le_ne_top
        [`int_f
         (Term.app
          `lintegral_mono
          [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ne_top_of_le_ne_top
       [`int_f
        (Term.app `lintegral_mono [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lintegral_mono [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lintegral_mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `lintegral_mono [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `int_f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_top_of_le_ne_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `fs [`x])
        " ∂"
        `μ)
       "≠"
       (Ennreal.Data.Real.Ennreal.ennreal.top "∞"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal.top "∞")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `fs [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fs [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `fs [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs_le_f)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `int_fs)])
             [])]
           "⟩")])]
       [":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `fs)]
           [":"
            (MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»
             `α
             " →ₛ "
             (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
         ","
         («term_∧_»
          (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `fs [`x]) "≤" (Term.app `f [`x])))
          "∧"
          («term_≤_»
           (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
            "∫⁻"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
            ", "
            (Term.app `f [`x])
            " ∂"
            `μ)
           "≤"
           («term_+_»
            (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
             "∫⁻"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             ", "
             (Term.app `fs [`x])
             " ∂"
             `μ)
            "+"
            («term_/_» `ε "/" (num "2"))))))]
       [":="
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                []
                ":="
                (Term.app
                 `Ennreal.lt_add_right
                 [`int_f (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))))
             []
             (Mathlib.Tactic.Conv.convRHS
              "conv_rhs"
              ["at" `this]
              []
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(Tactic.Conv.convRw__
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app
                      `lintegral_eq_nnreal
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [`x]
                         []
                         "=>"
                         (Term.typeAscription
                          "("
                          (Term.app `f [`x])
                          ":"
                          [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                          ")")))
                       `μ]))]
                   "]"))])))
             []
             (Std.Tactic.seq_focus
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ennreal.bsupr_add)] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
              "<;>"
              "["
              [(Tactic.skip "skip")
               ","
               (Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [(num "0")
                  ","
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`x]
                    []
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))]
                 "⟩"))]
              "]")
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `lt_supᵢ_iff)] "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `this)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs_le_f)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `int_fs)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`fs
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`x]
                  []
                  "=>"
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
                        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
                        ["using" (Term.app `fs_le_f [`x])]))])))))
                ","
                (Term.hole "_")]
               "⟩"))
             []
             (convert "convert" [] `int_fs.le [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 `simple_func.lintegral_eq_lintegral)]
               "]")
              [])
             []
             (Tactic.tacticRfl "rfl")])))]])
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
             []
             ":="
             (Term.app
              `Ennreal.lt_add_right
              [`int_f (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))))
          []
          (Mathlib.Tactic.Conv.convRHS
           "conv_rhs"
           ["at" `this]
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  []
                  (Term.app
                   `lintegral_eq_nnreal
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`x]
                      []
                      "=>"
                      (Term.typeAscription
                       "("
                       (Term.app `f [`x])
                       ":"
                       [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                       ")")))
                    `μ]))]
                "]"))])))
          []
          (Std.Tactic.seq_focus
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ennreal.bsupr_add)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           "<;>"
           "["
           [(Tactic.skip "skip")
            ","
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(num "0")
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))]
              "⟩"))]
           "]")
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `lt_supᵢ_iff)] "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `this)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs_le_f)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `int_fs)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [`fs
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
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
                     [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
                     ["using" (Term.app `fs_le_f [`x])]))])))))
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (convert "convert" [] `int_fs.le [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `simple_func.lintegral_eq_lintegral)]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `simple_func.lintegral_eq_lintegral)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simple_func.lintegral_eq_lintegral
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `int_fs.le [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `int_fs.le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [`fs
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
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
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
                 ["using" (Term.app `fs_le_f [`x])]))])))))
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`fs
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
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
                [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
                ["using" (Term.app `fs_le_f [`x])]))])))))
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
        [`x]
        []
        "=>"
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
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
              ["using" (Term.app `fs_le_f [`x])]))])))))
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
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
            ["using" (Term.app `fs_le_f [`x])]))])))
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
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Ennreal.coe_le_coe)] "]")]
        ["using" (Term.app `fs_le_f [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fs_le_f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs_le_f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `this)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `fs_le_f)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `int_fs)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `lt_supᵢ_iff)] "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lt_supᵢ_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.seq_focus
       (Tactic.tacticErw__
        "erw"
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ennreal.bsupr_add)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
       "<;>"
       "["
       [(Tactic.skip "skip")
        ","
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(num "0")
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))]
          "⟩"))]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(num "0")
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(num "0")
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.skip "skip")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ennreal.bsupr_add)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.bsupr_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convRHS
       "conv_rhs"
       ["at" `this]
       []
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.convRw__
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `lintegral_eq_nnreal
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`x]
                  []
                  "=>"
                  (Term.typeAscription
                   "("
                   (Term.app `f [`x])
                   ":"
                   [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                   ")")))
                `μ]))]
            "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lintegral_eq_nnreal
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.typeAscription
           "("
           (Term.app `f [`x])
           ":"
           [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
           ")")))
        `μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
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
        (Term.typeAscription
         "("
         (Term.app `f [`x])
         ":"
         [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
         ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `f [`x])
       ":"
       [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
       (Term.typeAscription
        "("
        (Term.app `f [`x])
        ":"
        [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
        ")")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lintegral_eq_nnreal
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
         []
         ":="
         (Term.app
          `Ennreal.lt_add_right
          [`int_f (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ennreal.lt_add_right
       [`int_f (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Ennreal.half_pos [`ε0]) "." `ne')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Ennreal.half_pos [`ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.half_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Ennreal.half_pos [`ε0]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `int_f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ennreal.lt_add_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `fs)]
         [":"
          (MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»
           `α
           " →ₛ "
           (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))]))
       ","
       («term_∧_»
        (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `fs [`x]) "≤" (Term.app `f [`x])))
        "∧"
        («term_≤_»
         (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
          "∫⁻"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app `f [`x])
          " ∂"
          `μ)
         "≤"
         («term_+_»
          (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
           "∫⁻"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
           ", "
           (Term.app `fs [`x])
           " ∂"
           `μ)
          "+"
          («term_/_» `ε "/" (num "2"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `fs [`x]) "≤" (Term.app `f [`x])))
       "∧"
       («term_≤_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `f [`x])
         " ∂"
         `μ)
        "≤"
        («term_+_»
         (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
          "∫⁻"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app `fs [`x])
          " ∂"
          `μ)
         "+"
         («term_/_» `ε "/" (num "2")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `f [`x])
        " ∂"
        `μ)
       "≤"
       («term_+_»
        (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
         "∫⁻"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         (Term.app `fs [`x])
         " ∂"
         `μ)
        "+"
        («term_/_» `ε "/" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
        "∫⁻"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `fs [`x])
        " ∂"
        `μ)
       "+"
       («term_/_» `ε "/" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `fs [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fs [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `fs [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
       "∫⁻"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `f [`x])
       " ∂"
       `μ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (MeasureTheory.MeasureTheory.Integral.Lebesgue.«term∫⁻_,_∂_»
      "∫⁻"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app `f [`x])
      " ∂"
      `μ)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `fs [`x]) "≤" (Term.app `f [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.app `fs [`x]) "≤" (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `fs [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 0, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `fs [`x]) "≤" (Term.app `f [`x])))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»
       `α
       " →ₛ "
       (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.«term_→ₛ_»', expected 'MeasureTheory.MeasureTheory.Integral.VitaliCaratheodory.term_→ₛ_._@.MeasureTheory.Integral.VitaliCaratheodory._hyg.9'
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
    Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
    function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
    `lintegral`.
    Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
  theorem
    exists_upper_semicontinuous_le_lintegral_le
    ( f : α → ℝ≥0 ) ( int_f : ∫⁻ x , f x ∂ μ ≠ ∞ ) { ε : ℝ≥0∞ } ( ε0 : ε ≠ 0 )
      :
        ∃
          g : α → ℝ≥0
          ,
          ∀ x , g x ≤ f x ∧ UpperSemicontinuous g ∧ ∫⁻ x , f x ∂ μ ≤ ∫⁻ x , g x ∂ μ + ε
    :=
      by
        obtain
            ⟨ fs , fs_le_f , int_fs ⟩
            : ∃ fs : α →ₛ ℝ≥0 , ∀ x , fs x ≤ f x ∧ ∫⁻ x , f x ∂ μ ≤ ∫⁻ x , fs x ∂ μ + ε / 2
            :=
              by
                have := Ennreal.lt_add_right int_f Ennreal.half_pos ε0 . ne'
                  conv_rhs at this => rw [ lintegral_eq_nnreal fun x => ( f x : ℝ≥0∞ ) μ ]
                  erw [ Ennreal.bsupr_add ] at this <;> [ skip , exact ⟨ 0 , fun x => by simp ⟩ ]
                  simp only [ lt_supᵢ_iff ] at this
                  rcases this with ⟨ fs , fs_le_f , int_fs ⟩
                  refine' ⟨ fs , fun x => by simpa only [ Ennreal.coe_le_coe ] using fs_le_f x , _ ⟩
                  convert int_fs.le
                  rw [ ← simple_func.lintegral_eq_lintegral ]
                  rfl
          have
            int_fs_lt_top
              : ∫⁻ x , fs x ∂ μ ≠ ∞
              :=
              by
                apply ne_top_of_le_ne_top int_f lintegral_mono fun x => _
                  simpa only [ Ennreal.coe_le_coe ] using fs_le_f x
          obtain
            ⟨ g , g_le_fs , gcont , gint ⟩
            :
              ∃
                g : α → ℝ≥0
                ,
                ∀ x , g x ≤ fs x ∧ UpperSemicontinuous g ∧ ∫⁻ x , fs x ∂ μ ≤ ∫⁻ x , g x ∂ μ + ε / 2
            :=
              fs.exists_upper_semicontinuous_le_lintegral_le int_fs_lt_top Ennreal.half_pos ε0 . ne'
          refine' ⟨ g , fun x => g_le_fs x . trans fs_le_f x , gcont , _ ⟩
          calc
            ∫⁻ x , f x ∂ μ ≤ ∫⁻ x , fs x ∂ μ + ε / 2 := int_fs
            _ ≤ ∫⁻ x , g x ∂ μ + ε / 2 + ε / 2 := add_le_add gint le_rfl
              _ = ∫⁻ x , g x ∂ μ + ε := by rw [ add_assoc , Ennreal.add_halves ]
#align
  measure_theory.exists_upper_semicontinuous_le_lintegral_le MeasureTheory.exists_upper_semicontinuous_le_lintegral_le

/-- Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_upper_semicontinuous_le_integral_le (f : α → ℝ≥0)
    (fint : Integrable (fun x => (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → ℝ≥0,
      (∀ x, g x ≤ f x) ∧
        UpperSemicontinuous g ∧
          Integrable (fun x => (g x : ℝ)) μ ∧ (∫ x, (f x : ℝ) ∂μ) - ε ≤ ∫ x, g x ∂μ :=
  by
  lift ε to ℝ≥0 using εpos.le
  rw [Nnreal.coe_pos, ← Ennreal.coe_pos] at εpos
  have If : (∫⁻ x, f x ∂μ) < ∞ := has_finite_integral_iff_of_nnreal.1 fint.has_finite_integral
  rcases exists_upper_semicontinuous_le_lintegral_le f If.ne εpos.ne' with ⟨g, gf, gcont, gint⟩
  have Ig : (∫⁻ x, g x ∂μ) < ∞ :=
    by
    apply lt_of_le_of_lt (lintegral_mono fun x => _) If
    simpa using gf x
  refine' ⟨g, gf, gcont, _, _⟩
  · refine'
      integrable.mono fint gcont.measurable.coe_nnreal_real.ae_measurable.ae_strongly_measurable _
    exact Filter.eventually_of_forall fun x => by simp [gf x]
  · rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
    · rw [sub_le_iff_le_add]
      convert Ennreal.to_real_mono _ gint
      · simp
      · rw [Ennreal.to_real_add Ig.ne Ennreal.coe_ne_top]
        simp
      · simpa using Ig.ne
    · apply Filter.eventually_of_forall
      simp
    · exact gcont.measurable.coe_nnreal_real.ae_measurable.ae_strongly_measurable
    · apply Filter.eventually_of_forall
      simp
    · exact fint.ae_strongly_measurable
#align
  measure_theory.exists_upper_semicontinuous_le_integral_le MeasureTheory.exists_upper_semicontinuous_le_integral_le

/-! ### Vitali-Carathéodory theorem -/


/-- **Vitali-Carathéodory Theorem**: given an integrable real function `f`, there exists an
integrable function `g > f` which is lower semicontinuous, with integral arbitrarily close
to that of `f`. This function has to be `ereal`-valued in general. -/
theorem exists_lt_lower_semicontinuous_integral_lt [SigmaFinite μ] (f : α → ℝ) (hf : Integrable f μ)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → Ereal,
      (∀ x, (f x : Ereal) < g x) ∧
        LowerSemicontinuous g ∧
          Integrable (fun x => Ereal.toReal (g x)) μ ∧
            (∀ᵐ x ∂μ, g x < ⊤) ∧ (∫ x, Ereal.toReal (g x) ∂μ) < (∫ x, f x ∂μ) + ε :=
  by
  let δ : ℝ≥0 := ⟨ε / 2, (half_pos εpos).le⟩
  have δpos : 0 < δ := half_pos εpos
  let fp : α → ℝ≥0 := fun x => Real.toNnreal (f x)
  have int_fp : integrable (fun x => (fp x : ℝ)) μ := hf.real_to_nnreal
  rcases exists_lt_lower_semicontinuous_integral_gt_nnreal fp int_fp δpos with
    ⟨gp, fp_lt_gp, gpcont, gp_lt_top, gp_integrable, gpint⟩
  let fm : α → ℝ≥0 := fun x => Real.toNnreal (-f x)
  have int_fm : integrable (fun x => (fm x : ℝ)) μ := hf.neg.real_to_nnreal
  rcases exists_upper_semicontinuous_le_integral_le fm int_fm δpos with
    ⟨gm, gm_le_fm, gmcont, gm_integrable, gmint⟩
  let g : α → Ereal := fun x => (gp x : Ereal) - gm x
  have ae_g : ∀ᵐ x ∂μ, (g x).toReal = (gp x : Ereal).toReal - (gm x : Ereal).toReal :=
    by
    filter_upwards [gp_lt_top] with _ hx
    rw [Ereal.to_real_sub] <;> simp [hx.ne]
  refine' ⟨g, _, _, _, _, _⟩
  show integrable (fun x => Ereal.toReal (g x)) μ
  · rw [integrable_congr ae_g]
    convert gp_integrable.sub gm_integrable
    ext x
    simp
  show (∫ x : α, (g x).toReal ∂μ) < (∫ x : α, f x ∂μ) + ε
  exact
    calc
      (∫ x : α, (g x).toReal ∂μ) = ∫ x : α, Ereal.toReal (gp x) - Ereal.toReal (gm x) ∂μ :=
        integral_congr_ae ae_g
      _ = (∫ x : α, Ereal.toReal (gp x) ∂μ) - ∫ x : α, gm x ∂μ :=
        by
        simp only [Ereal.to_real_coe_ennreal, Ennreal.coe_to_real, coe_coe]
        exact integral_sub gp_integrable gm_integrable
      _ < (∫ x : α, ↑(fp x) ∂μ) + ↑δ - ∫ x : α, gm x ∂μ :=
        by
        apply sub_lt_sub_right
        convert gpint
        simp only [Ereal.to_real_coe_ennreal]
      _ ≤ (∫ x : α, ↑(fp x) ∂μ) + ↑δ - ((∫ x : α, fm x ∂μ) - δ) := sub_le_sub_left gmint _
      _ = (∫ x : α, f x ∂μ) + 2 * δ :=
        by
        simp_rw [integral_eq_integral_pos_part_sub_integral_neg_part hf, fp, fm]
        ring
      _ = (∫ x : α, f x ∂μ) + ε := by
        congr 1
        field_simp [δ, mul_comm]
      
  show ∀ᵐ x : α ∂μ, g x < ⊤
  · filter_upwards [gp_lt_top] with _ hx
    simp only [g, sub_eq_add_neg, coe_coe, Ne.def, (Ereal.add_lt_top _ _).Ne, lt_top_iff_ne_top,
      lt_top_iff_ne_top.1 hx, Ereal.coe_ennreal_eq_top_iff, not_false_iff, Ereal.neg_eq_top_iff,
      Ereal.coe_ennreal_ne_bot]
  show ∀ x, (f x : Ereal) < g x
  · intro x
    rw [Ereal.coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal (f x)]
    refine' Ereal.sub_lt_sub_of_lt_of_le _ _ _ _
    · simp only [Ereal.coe_ennreal_lt_coe_ennreal_iff, coe_coe]
      exact fp_lt_gp x
    · simp only [Ennreal.coe_le_coe, Ereal.coe_ennreal_le_coe_ennreal_iff, coe_coe]
      exact gm_le_fm x
    · simp only [Ereal.coe_ennreal_ne_bot, Ne.def, not_false_iff, coe_coe]
    · simp only [Ereal.coe_nnreal_ne_top, Ne.def, not_false_iff, coe_coe]
  show LowerSemicontinuous g
  · apply LowerSemicontinuous.add'
    ·
      exact
        continuous_coe_ennreal_ereal.comp_lower_semicontinuous gpcont fun x y hxy =>
          Ereal.coe_ennreal_le_coe_ennreal_iff.2 hxy
    · apply
        ereal.continuous_neg.comp_upper_semicontinuous_antitone _ fun x y hxy =>
          Ereal.neg_le_neg_iff.2 hxy
      dsimp
      apply
        continuous_coe_ennreal_ereal.comp_upper_semicontinuous _ fun x y hxy =>
          Ereal.coe_ennreal_le_coe_ennreal_iff.2 hxy
      exact
        ennreal.continuous_coe.comp_upper_semicontinuous gmcont fun x y hxy =>
          Ennreal.coe_le_coe.2 hxy
    · intro x
      exact Ereal.continuous_at_add (by simp) (by simp)
#align
  measure_theory.exists_lt_lower_semicontinuous_integral_lt MeasureTheory.exists_lt_lower_semicontinuous_integral_lt

/-- **Vitali-Carathéodory Theorem**: given an integrable real function `f`, there exists an
integrable function `g < f` which is upper semicontinuous, with integral arbitrarily close to that
of `f`. This function has to be `ereal`-valued in general. -/
theorem exists_upper_semicontinuous_lt_integral_gt [SigmaFinite μ] (f : α → ℝ) (hf : Integrable f μ)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → Ereal,
      (∀ x, (g x : Ereal) < f x) ∧
        UpperSemicontinuous g ∧
          Integrable (fun x => Ereal.toReal (g x)) μ ∧
            (∀ᵐ x ∂μ, ⊥ < g x) ∧ (∫ x, f x ∂μ) < (∫ x, Ereal.toReal (g x) ∂μ) + ε :=
  by
  rcases exists_lt_lower_semicontinuous_integral_lt (fun x => -f x) hf.neg εpos with
    ⟨g, g_lt_f, gcont, g_integrable, g_lt_top, gint⟩
  refine' ⟨fun x => -g x, _, _, _, _, _⟩
  · exact fun x => Ereal.neg_lt_iff_neg_lt.1 (by simpa only [Ereal.coe_neg] using g_lt_f x)
  ·
    exact
      ereal.continuous_neg.comp_lower_semicontinuous_antitone gcont fun x y hxy =>
        Ereal.neg_le_neg_iff.2 hxy
  · convert g_integrable.neg
    ext x
    simp
  · simpa [bot_lt_iff_ne_bot, lt_top_iff_ne_top] using g_lt_top
  · simp_rw [integral_neg, lt_neg_add_iff_add_lt] at gint
    rw [add_comm] at gint
    simpa [integral_neg] using gint
#align
  measure_theory.exists_upper_semicontinuous_lt_integral_gt MeasureTheory.exists_upper_semicontinuous_lt_integral_gt

end MeasureTheory

